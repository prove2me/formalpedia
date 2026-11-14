-- Prove2me | solution 1 for QuantileMDP.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-13T18:03:29.073905+00:00
-- url     : https://prove2.me/submissions/8f88a4a8-afd1-4574-9142-7e09479ad6a9

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_QuantileMDP_eq_7
import Theorems.Thm_QuantileMDP_lemma_2
import Definitions.Def_QuantileMDP_optValue

open MeasureTheory ProbabilityTheory Set QuantileMDP
open scoped ENNReal

namespace QuantileMDP

private theorem transition_sum {S : Type*} [Fintype S] (p : PMF S) :
    ∑ s, p s = 1 := by
  exact (tsum_fintype (fun s => p s)).symm.trans p.tsum_coe

private theorem rewardLaw_zero {S A : Type*} [Fintype S] (M : Model S A)
    (π : Policy S A) (s : S) : rewardLaw M 0 π s = Measure.dirac 0 := by
  simp [rewardLaw, pathWeight, pathReward]

private theorem tail_admissible {S A : Type*} (M : Model S A) (t : ℕ) (π : Policy S A)
    (hπ : (M.shift t).Admissible π) (s : S) :
    (M.shift (t + 1)).Admissible (π.tail s) := by
  intro k h
  simpa [Model.shift, Policy.tail, Fin.cons_last, Nat.add_left_comm, Nat.add_comm] using
    hπ (k + 1) (Fin.cons s h)

private theorem rewardLaw_prob {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (n t : ℕ) (π : Policy S A) (s : S)
    (hπ : (M.shift t).Admissible π) : IsProbabilityMeasure (rewardLaw (M.shift t) n π s) := by
  induction n generalizing t π s with
  | zero =>
    rw [rewardLaw_zero]
    infer_instance
  | succ n ih =>
    have ht : t < t + (n + 1) := by omega
    have he := (eq_7 M (t + (n + 1)) t ht s (π 0 (fun _ => s))).1 π hπ rfl
    have hn : t + (n + 1) - t = n + 1 := by omega
    have hn' : t + (n + 1) - (t + 1) = n := by omega
    rw [hn, hn'] at he
    constructor
    rw [he, Measure.finsetSum_apply _ _ _]
    rw [← transition_sum (M.P t s (π 0 (fun _ => s)))]
    apply Finset.sum_congr rfl
    intro i _
    have hm : Measurable (fun x : ℝ => x + M.r t s (π 0 (fun _ => s)) i) :=
      measurable_id.add_const _
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hm MeasurableSet.univ,
      preimage_univ, (ih (t + 1) (π.tail s) i (tail_admissible M t π hπ s)).measure_univ,
      mul_one]

private theorem pathWeight_sum {S A : Type*} [Fintype S] (M : Model S A)
    (n : ℕ) (π : Policy S A) (s : S) [IsProbabilityMeasure (rewardLaw M n π s)] :
    ∑ g : Fin n → S, pathWeight M π (Fin.cons s g) = 1 := by
  have h : rewardLaw M n π s univ = 1 := measure_univ
  simpa [rewardLaw, Measure.finsetSum_apply _ _ _, Measure.smul_apply,
    smul_eq_mul] using h

/-- A finite-horizon policy is observed only on histories strictly before the horizon. -/
private theorem rewardLaw_congr {S A : Type*} [Fintype S] (M : Model S A)
    (n : ℕ) (π ρ : Policy S A) (s : S)
    (h : ∀ k < n, π k = ρ k) :
    rewardLaw M n π s = rewardLaw M n ρ s := by
  unfold rewardLaw
  apply Finset.sum_congr rfl
  intro g _
  have hw : pathWeight M π (Fin.cons s g) = pathWeight M ρ (Fin.cons s g) := by
    unfold pathWeight
    exact Finset.prod_congr rfl fun i _ => by rw [h i i.isLt]
  have hr : pathReward M π (Fin.cons s g) = pathReward M ρ (Fin.cons s g) := by
    unfold pathReward
    exact Finset.sum_congr rfl fun i _ => by rw [h i i.isLt]
  rw [hw, hr]

private theorem greatest_policy {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (n : ℕ) (s : S) (q : ℝ) (good : Set (Policy S A))
    (hgood : good.Nonempty) :
    ∃ π ∈ good, ∀ ρ ∈ good, quantile (rewardLaw M n ρ s) q ≤
      quantile (rewardLaw M n π s) q := by
  classical
  let Obs := (k : Fin n) → (Fin (k.val + 1) → S) → A
  let observe : Policy S A → Obs := fun π k => π k.val
  let value : Policy S A → EReal := fun π => quantile (rewardLaw M n π s) q
  let image := value '' good
  obtain ⟨d, hd⟩ := hgood
  have hfin : image.Finite := by
    let extend : Obs → Policy S A := fun f k h =>
      if hk : k < n then f ⟨k, hk⟩ h else d k h
    refine (finite_range (value ∘ extend)).subset ?_
    rintro _ ⟨π, _, rfl⟩
    refine ⟨observe π, ?_⟩
    change value (extend (observe π)) = value π
    unfold value
    rw [rewardLaw_congr M n (extend (observe π)) π s
      (fun k hk => by funext h; simp [extend, observe, hk])]
  obtain ⟨_, ⟨π, hπ, rfl⟩, hmax⟩ := image.exists_max_image id hfin ⟨value d, d, hd, rfl⟩
  exact ⟨π, hπ, fun ρ hρ => hmax _ ⟨ρ, hρ, rfl⟩⟩

private theorem optimal_policy {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (T t : ℕ) (s : S) (q : ℝ) :
    ∃ π : Policy S A, (M.shift t).Admissible π ∧
      quantile (rewardLaw (M.shift t) (T - t) π s) q = optValue M T t s q := by
  let d : Policy S A := fun k h => ((M.shift t).adm_nonempty k (h (Fin.last k))).choose
  have hd : (M.shift t).Admissible d := fun k h =>
    ((M.shift t).adm_nonempty k (h (Fin.last k))).choose_spec
  obtain ⟨π, hπ, hmax⟩ := greatest_policy (M.shift t) (T - t) s q
    {π | (M.shift t).Admissible π} ⟨d, hd⟩
  refine ⟨π, hπ, le_antisymm (le_iSup_of_le π (le_iSup_of_le hπ le_rfl)) ?_⟩
  exact iSup_le fun ρ => iSup_le fun hρ => hmax ρ hρ

/-- Combine a fixed first action with separate continuation policies for each successor. -/
private noncomputable def splice {S A : Type*} [DecidableEq S]
    (M : Model S A) (t : ℕ) (s : S) (a : A) (ρ : S → Policy S A) : Policy S A
  | 0, h => if h 0 = s then a else (M.adm_nonempty t (h 0)).choose
  | k + 1, h => ρ (h 1) k (Fin.tail h)

private theorem splice_admissible {S A : Type*} [DecidableEq S]
    (M : Model S A) (t : ℕ) (s : S) (a : A) (ha : a ∈ M.adm t s)
    (ρ : S → Policy S A) (hρ : ∀ z, (M.shift (t + 1)).Admissible (ρ z)) :
    (M.shift t).Admissible (splice M t s a ρ) := by
  intro k h
  cases k with
  | zero =>
    have hl : Fin.last 0 = 0 := Fin.eq_zero _
    rw [hl]
    by_cases hh : h 0 = s
    · simpa [splice, Model.shift, hh] using ha
    · simpa [splice, Model.shift, hh] using (M.adm_nonempty t (h 0)).choose_spec
  | succ k =>
    simpa [splice, Model.shift, Fin.tail, Nat.add_left_comm, Nat.add_comm] using
      hρ (h 1) k (Fin.tail h)

/-- Reward laws only depend on the policy on histories starting at the given state. -/
private theorem rewardLaw_congr_start {S A : Type*} [Fintype S] (M : Model S A)
    (n : ℕ) (π ρ : Policy S A) (s : S)
    (h : ∀ k (g : Fin (k + 1) → S), g 0 = s → π k g = ρ k g) :
    rewardLaw M n π s = rewardLaw M n ρ s := by
  have hp (g : Fin n → S) (i : Fin n) : pathPrefix (Fin.cons s g) i 0 = s := by
    rfl
  unfold rewardLaw
  apply Finset.sum_congr rfl
  intro g _
  have hw : pathWeight M π (Fin.cons s g) = pathWeight M ρ (Fin.cons s g) := by
    unfold pathWeight
    exact Finset.prod_congr rfl fun i _ => by rw [h _ _ (hp g i)]
  have hr : pathReward M π (Fin.cons s g) = pathReward M ρ (Fin.cons s g) := by
    unfold pathReward
    exact Finset.sum_congr rfl fun i _ => by rw [h _ _ (hp g i)]
  rw [hw, hr]

private theorem splice_rewardLaw {S A : Type*} [Fintype S] [DecidableEq S]
    (M : Model S A) (t n : ℕ) (s aState : S) (a : A) (ρ : S → Policy S A) :
    rewardLaw (M.shift (t + 1)) n ((splice M t s a ρ).tail s) aState =
      rewardLaw (M.shift (t + 1)) n (ρ aState) aState := by
  apply rewardLaw_congr_start
  intro k g hg
  simpa [Policy.tail, splice, Fin.tail_cons, Fin.cons_succ] using
    congrArg (fun z => ρ z k g) hg

private theorem quantile_map_add (μ : Measure ℝ) (c τ : ℝ) :
    quantile (μ.map (fun x => x + c)) τ = quantile μ τ + (c : EReal) := by
  let e : EReal ≃o EReal :=
    { toFun := fun x => x + (c : EReal)
      invFun := fun x => x - (c : EReal)
      left_inv := fun _ => EReal.add_sub_cancel_right
      right_inv := fun _ => EReal.sub_add_cancel
      map_rel_iff' := (EReal.addLECancellable_coe c).add_le_add_iff_right }
  have hm : Measurable (fun y : ℝ => y + c) := measurable_id.add_const c
  have h₁ (x : ℝ) : (μ.map (fun y => y + c)) (Ici x) = μ (Ici (x - c)) := by
    rw [Measure.map_apply hm measurableSet_Ici]
    congr 1
    ext y
    change (x ≤ y + c) ↔ (x - c ≤ y)
    exact sub_le_iff_le_add.symm
  have h₂ (x : ℝ) : (μ.map (fun y => y + c)) (Iic x) = μ (Iic (x - c)) := by
    rw [Measure.map_apply hm measurableSet_Iic]
    congr 1
    ext y
    change (y + c ≤ x) ↔ (y ≤ x - c)
    exact le_sub_iff_add_le.symm
  have himage (p : ℝ → Prop) :
      (fun x : ℝ => (x : EReal)) '' {x | p (x - c)} =
        e '' ((fun x : ℝ => (x : EReal)) '' {x | p x}) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨((x - c : ℝ) : EReal), ⟨x - c, hx, rfl⟩,
        by change ((x - c : ℝ) : EReal) + (c : EReal) = (x : EReal); rw [← EReal.coe_add, sub_add_cancel]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x + c, by simpa using hx, EReal.coe_add _ _⟩
  change _ = e (quantile μ τ)
  simp only [quantile, h₁, h₂]
  split_ifs
  · rw [himage (fun x => μ (Ici x) = 1)]
    rw [sSup_image, ← e.map_sSup]
  · rw [himage (fun x => μ (Iic x) = 1)]
    rw [sInf_image, ← e.map_sInf]
  · rw [himage (fun x => ENNReal.ofReal τ ≤ μ (Iic x))]
    rw [sInf_image, ← e.map_sInf]

/-- Apply the one-hot form of Lemma 2 on the finite space of successor states
and continuation paths. A zero-probability successor can be dropped from OPT. -/
private theorem reward_mixture {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (t n : ℕ) (s : S) (a : A) (ρ : S → Policy S A)
    (hρ : ∀ i, (M.shift (t + 1)).Admissible (ρ i))
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    let p := fun i => M.P t s a i
    let ν := fun i => (rewardLaw (M.shift (t + 1)) n (ρ i) i).map
      (fun x => x + M.r t s a i)
    quantile (∑ i, p i • ν i) τ = opt (fun i => (p i).toReal)
      (fun i q => quantile (ν i) q) τ ∧
    OptAttained (fun i => (p i).toReal) (fun i q => quantile (ν i) q) τ := by
  classical
  dsimp
  let p := fun i => M.P t s a i
  let ν := fun i => (rewardLaw (M.shift (t + 1)) n (ρ i) i).map
    (fun x => x + M.r t s a i)
  let Ω := S × (Fin n → S)
  let : MeasurableSpace Ω := ⊤
  have hmeas (B : Set Ω) : MeasurableSet B := by trivial
  let w : Ω → ℝ≥0∞ := fun z =>
    pathWeight (M.shift (t + 1)) (ρ z.1) (Fin.cons z.1 z.2)
  let X : S → Ω → ℝ := fun i z =>
    pathReward (M.shift (t + 1)) (ρ i) (Fin.cons i z.2) + M.r t s a i
  let Y : S → Ω → ℝ := fun i z => if z.1 = i then 1 else 0
  let P : Measure Ω := ∑ z : Ω, (p z.1 * w z) • Measure.dirac z
  let B : S → Set Ω := fun i => {z | z.1 = i}
  have hw (i : S) : ∑ g : Fin n → S, w (i, g) = 1 := by
    let := rewardLaw_prob M n (t + 1) (ρ i) i (hρ i)
    exact pathWeight_sum (M.shift (t + 1)) n (ρ i) i
  have hP (U : Set Ω) : P U = ∑ i : S, ∑ g : Fin n → S,
      if (i, g) ∈ U then p i * w (i, g) else 0 := by
    unfold P
    rw [Measure.finsetSum_apply _ _ _, Fintype.sum_prod_type]
    simp only [Measure.smul_apply, Measure.dirac_apply' _ (hmeas U), smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro g _
    by_cases h : (i, g) ∈ U <;> simp [h, Set.indicator]
  let : IsProbabilityMeasure P := ⟨by
    simp only [hP, mem_univ, if_true, ← Finset.mul_sum, hw, mul_one]
    exact transition_sum _⟩
  have hB (i : S) (U : Set Ω) : P (B i ∩ U) = p i *
      ∑ g : Fin n → S, if (i, g) ∈ U then w (i, g) else 0 := by
    rw [hP, Finset.sum_eq_single i]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      have h : (i, g) ∈ B i ∩ U ↔ (i, g) ∈ U := by
        change (i = i ∧ (i, g) ∈ U) ↔ _
        simp
      by_cases hu : (i, g) ∈ U
      · rw [if_pos hu, if_pos (h.mpr hu)]
      · rw [if_neg hu, if_neg (fun hmem => hu (h.mp hmem)), mul_zero]
    · intro j _ hji
      refine Finset.sum_eq_zero fun g _ => if_neg ?_
      exact fun h => hji h.1
    · simp
  have hp (i : S) : P (B i) = p i := by
    simpa [hw] using hB i univ
  have hX (i : S) : Measurable (X i) := fun U _ => hmeas _
  have hY (i : S) : Measurable (Y i) := fun U _ => hmeas _
  have hY01 (i : S) (z : Ω) : Y i z = 0 ∨ Y i z = 1 := by
    by_cases h : z.1 = i <;> simp [Y, h]
  have hZ (z : Ω) : (∑ i, X i z * Y i z) = X z.1 z := by
    simp [Y, mul_ite]
  have hYsum (z : Ω) : ∑ i, Y i z = 1 := by simp [Y]
  have hν (i : S) (U : Set ℝ) (hU : MeasurableSet U) :
      ν i U = ∑ g : Fin n → S, if X i (i, g) ∈ U then w (i, g) else 0 := by
    have hm : Measurable (fun x : ℝ => x + M.r t s a i) := measurable_id.add_const _
    unfold ν rewardLaw
    rw [Measure.map_apply hm hU, Measure.finsetSum_apply _ _ _]
    apply Finset.sum_congr rfl
    intro g _
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply]
    change w (i, g) * (indicator ((fun x : ℝ => x + M.r t s a i) ⁻¹' U) 1)
      (pathReward (M.shift (t + 1)) (ρ i) (Fin.cons i g)) =
        if X i (i, g) ∈ U then w (i, g) else 0
    rw [Set.indicator]
    change (w (i, g) * (if X i (i, g) ∈ U then 1 else 0)) = _
    split_ifs <;> simp
  have htotal : P.map (fun z => ∑ i, X i z * Y i z) = ∑ i, p i • ν i := by
    ext U hU
    rw [Measure.map_apply (fun V _ => hmeas _) hU, hP, Measure.finsetSum_apply _ _ _]
    apply Finset.sum_congr rfl
    intro i _
    rw [Measure.smul_apply, smul_eq_mul, hν _ _ hU, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    change (if (∑ j, X j (i, g) * Y j (i, g)) ∈ U then _ else _) = _
    rw [hZ]
    split_ifs <;> simp
  have hbranch (i : S) : {z | Y i z = 1} = B i := by
    ext z
    by_cases h : z.1 = i <;> simp [Y, B, h]
  have hcond (i : S) (hi : p i ≠ 0) : (P[|B i]).map (X i) = ν i := by
    ext U hU
    rw [Measure.map_apply (hX i) hU, cond_apply (hmeas _), hB, hp, hν _ _ hU,
      ENNReal.inv_mul_cancel_left hi (PMF.apply_ne_top _ _)]
    rfl
  let g : S → ℝ → EReal := fun i q => quantile ((P[|{z | Y i z = 1}]).map (X i)) q
  let g' : S → ℝ → EReal := fun i q => quantile (ν i) q
  have hpos (i : S) (hi : (p i).toReal ≠ 0) : g i = g' i := by
    funext q
    unfold g g'
    rw [hbranch, hcond i (fun h => hi (by simp [h]))]
  have hL := lemma_2 P X Y hX (fun i => finite_range (X i)) hY hY01 hYsum τ hτ
  simp_rw [htotal, hbranch, hp] at hL
  change quantile (∑ i, p i • ν i) τ = opt (fun i => (p i).toReal)
      (fun i q => quantile ((P[|B i]).map (X i)) q) τ ∧
    OptAttained (fun i => (p i).toReal) (fun i q => quantile ((P[|B i]).map (X i)) q) τ at hL
  have hL' : quantile (∑ i, p i • ν i) τ = opt (fun i => (p i).toReal) g τ ∧
      OptAttained (fun i => (p i).toReal) g τ := by simpa only [g, hbranch] using hL
  let trim (q : S → ℝ) (i : S) := if (p i).toReal = 0 then 1 else q i
  have htrim (q : S → ℝ) (hq : q ∈ Feasible (fun i => (p i).toReal) τ) :
      trim q ∈ Feasible (fun i => (p i).toReal) τ := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi : (p i).toReal = 0 <;> simp [trim, hi, hq.1 i]
    · have he : ∑ i, (p i).toReal * trim q i = ∑ i, (p i).toReal * q i := by
        exact Finset.sum_congr rfl fun i _ => by by_cases hi : (p i).toReal = 0 <;> simp [trim, hi]
      rw [he]
      exact hq.2
  have hinf (f f' : S → ℝ → EReal)
      (hf : ∀ i, (p i).toReal ≠ 0 → f i = f' i) (q : S → ℝ) :
      (⨅ i, ⨅ (_ : q i ≠ 1), f i (q i)) ≤
        ⨅ i, ⨅ (_ : trim q i ≠ 1), f' i (trim q i) := by
    refine le_iInf fun i => le_iInf fun hi => ?_
    have hpne : (p i).toReal ≠ 0 := fun h => hi (by simp [trim, h])
    rw [show trim q i = q i by simp [trim, hpne]] at hi ⊢
    rw [← hf i hpne]
    exact iInf_le_of_le i (iInf_le _ hi)
  have hopt (f f' : S → ℝ → EReal) (hf : ∀ i, (p i).toReal ≠ 0 → f i = f' i) :
      opt (fun i => (p i).toReal) f τ ≤ opt (fun i => (p i).toReal) f' τ :=
    iSup_le fun q => iSup_le fun hq =>
      (hinf f f' hf q).trans (le_iSup_of_le (trim q) (le_iSup_of_le (htrim q hq) le_rfl))
  have he := le_antisymm (hopt g g' hpos) (hopt g' g fun i hi => (hpos i hi).symm)
  obtain ⟨q, hq, hqopt⟩ := hL'.2
  refine ⟨hL'.1.trans he, ⟨trim q, htrim q hq, le_antisymm ?_ ?_⟩⟩
  · exact le_iSup_of_le (trim q) (le_iSup_of_le (htrim q hq) le_rfl)
  · rw [← he, ← hqopt]
    exact hinf g g' hpos q

end QuantileMDP

/-- The fixed-action value equals the branch allocation problem and both are attained. -/
theorem solution {S A : Type*} [Fintype S] [Fintype A] (M : Model S A) (T t : ℕ) (ht : t < T)
    (s : S) (a : A) (ha : a ∈ M.adm t s) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    optValueAct M T t s τ a =
        opt (fun s' => (M.P t s a s').toReal)
          (fun s' q => optValue M T (t + 1) s' q + ((M.r t s a s' : ℝ) : EReal)) τ ∧
      OptAttained (fun s' => (M.P t s a s').toReal)
        (fun s' q => optValue M T (t + 1) s' q + ((M.r t s a s' : ℝ) : EReal)) τ ∧
      ∃ π : Policy S A, (M.shift t).Admissible π ∧ π 0 (fun _ => s) = a ∧
        quantile (rewardLaw (M.shift t) (T - t) π s) τ = optValueAct M T t s τ a := by
  classical
  let n := T - (t + 1)
  let p := fun i => (M.P t s a i).toReal
  let v := fun i q => optValue M T (t + 1) i q + (M.r t s a i : EReal)
  let value := fun π => quantile (rewardLaw (M.shift t) (T - t) π s) τ
  let branch := fun (ρ : S → Policy S A) i q =>
    quantile (rewardLaw (M.shift (t + 1)) n (ρ i) i) q + (M.r t s a i : EReal)
  have hmix (π : Policy S A) (hπ : (M.shift t).Admissible π) (hfirst : π 0 (fun _ => s) = a)
      (ρ : S → Policy S A) (hρ : ∀ i, (M.shift (t + 1)).Admissible (ρ i))
      (he : ∀ i, rewardLaw (M.shift (t + 1)) n (π.tail s) i =
        rewardLaw (M.shift (t + 1)) n (ρ i) i) :
      value π = opt p (branch ρ) τ ∧ OptAttained p (branch ρ) τ := by
    have hlaw := (eq_7 M T t ht s a).1 π hπ hfirst
    change rewardLaw (M.shift t) (T - t) π s =
      ∑ i, M.P t s a i • (rewardLaw (M.shift (t + 1)) n (π.tail s) i).map
        (fun x => x + M.r t s a i) at hlaw
    simp_rw [he] at hlaw
    have hh := reward_mixture M t n s a ρ hρ τ hτ
    dsimp only at hh
    simpa only [value, hlaw, quantile_map_add, p, branch] using hh
  have hle (ρ : S → Policy S A) (hρ : ∀ i, (M.shift (t + 1)).Admissible (ρ i)) :
      ∀ i q, branch ρ i q ≤ v i q := by
    intro i q
    apply add_le_add_left
    exact le_iSup_of_le (ρ i) (le_iSup_of_le (hρ i) le_rfl)
  have hupper : optValueAct M T t s τ a ≤ opt p v τ := by
    refine iSup_le fun π => iSup_le fun hπ => iSup_le fun haπ => ?_
    let ρ : S → Policy S A := fun _ => π.tail s
    have hρ : ∀ i, (M.shift (t + 1)).Admissible (ρ i) := fun _ => tail_admissible M t π hπ s
    change value π ≤ opt p v τ
    rw [(hmix π hπ haπ ρ hρ (fun _ => rfl)).1]
    exact iSup_le fun q => iSup_le fun hq =>
      le_iSup_of_le q (le_iSup_of_le hq (iInf_mono fun i => iInf_mono fun _ => hle ρ hρ i (q i)))
  have hrealize (q : S → ℝ) (hq : q ∈ Feasible p τ) :
      ∃ π : Policy S A, ∃ hπ : (M.shift t).Admissible π, ∃ hfirst : π 0 (fun _ => s) = a,
        (⨅ i, ⨅ (_ : q i ≠ 1), v i (q i)) ≤ value π := by
    choose ρ hρ hval using fun i => optimal_policy M T (t + 1) i (q i)
    let π := splice M t s a ρ
    have hπ := splice_admissible M t s a ha ρ hρ
    have hfirst : π 0 (fun _ => s) = a := by simp [π, splice]
    refine ⟨π, hπ, hfirst, ?_⟩
    rw [(hmix π hπ hfirst ρ hρ (fun i => splice_rewardLaw M t n s i a ρ)).1]
    apply le_iSup_of_le q
    apply le_iSup_of_le hq
    simp only [v, branch, n, hval, le_refl]
  have hlower : opt p v τ ≤ optValueAct M T t s τ a := by
    refine iSup_le fun q => iSup_le fun hq => ?_
    obtain ⟨π, hπ, hfirst, hvalue⟩ := hrealize q hq
    exact hvalue.trans (le_iSup_of_le π (le_iSup_of_le hπ (le_iSup_of_le hfirst le_rfl)))
  -- The fixed-action supremum is attained because the finite-horizon policy image is finite.
  have hmax : ∃ π : Policy S A, (M.shift t).Admissible π ∧ π 0 (fun _ => s) = a ∧
      value π = optValueAct M T t s τ a := by
    let d : Policy S A := fun k h => ((M.shift (t + 1)).adm_nonempty k (h (Fin.last k))).choose
    let π₀ := splice M t s a (fun _ => d)
    have hπ₀ : (M.shift t).Admissible π₀ :=
      splice_admissible M t s a ha _ fun _ k h =>
        ((M.shift (t + 1)).adm_nonempty k (h (Fin.last k))).choose_spec
    have hfirst₀ : π₀ 0 (fun _ => s) = a := by simp [π₀, splice]
    obtain ⟨π, ⟨hπ, hfirst⟩, hbest⟩ := greatest_policy (M.shift t) (T - t) s τ
      {π | (M.shift t).Admissible π ∧ π 0 (fun _ => s) = a} ⟨π₀, hπ₀, hfirst₀⟩
    refine ⟨π, hπ, hfirst, le_antisymm
      (le_iSup_of_le π (le_iSup_of_le hπ (le_iSup_of_le hfirst le_rfl))) ?_⟩
    exact iSup_le fun ρ => iSup_le fun hρ => iSup_le fun h => hbest ρ ⟨hρ, h⟩
  have hopt := le_antisymm hupper hlower
  obtain ⟨π, hπ, hfirst, hval⟩ := hmax
  let ρ : S → Policy S A := fun _ => π.tail s
  have hρ : ∀ i, (M.shift (t + 1)).Admissible (ρ i) := fun _ => tail_admissible M t π hπ s
  have hm := hmix π hπ hfirst ρ hρ (fun _ => rfl)
  obtain ⟨q, hq, hqval⟩ := hm.2
  refine ⟨hopt, ⟨q, hq, le_antisymm
    (le_iSup_of_le q (le_iSup_of_le hq le_rfl)) ?_⟩, π, hπ, hfirst, hval⟩
  rw [← hopt, ← hval, hm.1, ← hqval]
  exact iInf_mono fun i => iInf_mono fun _ => hle ρ hρ i (q i)
