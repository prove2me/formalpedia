-- Prove2me | solution 1 for StochFictPlay.Supermodular.thm54_cooperative_irreducible_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T15:25:12.023775+00:00
-- url     : https://prove2.me/submissions/8a4a7ed9-d386-4f97-8685-21a464d0ac5b

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel_v2
import Definitions.Def_StochFictPlay_Supermodular_Game_v2
import Definitions.Def_StochFictPlay_Supermodular_StochOrder_v2
import Definitions.Def_StochFictPlay_Supermodular_Cooperative_v2

open MeasureTheory
open scoped ENNReal

namespace SF90
open StochFictPlay.Supermodular

theorem line_deriv {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π v : Fin m → ℝ)
    (i : Fin m) :
    HasDerivAt (fun t : ℝ => choiceProb f (π + t • v) i) (fderiv ℝ (choiceProb f) π v i) 0 := by
  have hd : Differentiable ℝ (choiceProb f) := hf.2.2.2.2.differentiable (by simp)
  have h1 : HasDerivAt (fun t : ℝ => π + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add π
  have hC : HasFDerivAt (choiceProb f) (fderiv ℝ (choiceProb f) π) (π + (0:ℝ) • v) := by
    simpa using (hd π).hasFDerivAt
  have := hC.comp_hasDerivAt (0:ℝ) h1
  exact hasDerivAt_pi.1 this i

theorem shift_inv {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (π : Fin m → ℝ) (t : ℝ) :
    choiceProb f (π + t • (1 : Fin m → ℝ)) = choiceProb f π := by
  funext i
  unfold choiceProb
  congr 2
  ext e
  simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  constructor
  · intro h j hj; have := h j hj; linarith
  · intro h j hj; have := h j hj; linarith

theorem row_sum {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (i : Fin m) : ∑ j : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i = 0 := by
  have h := line_deriv f hf π 1 i
  simp only [shift_inv] at h
  have h0 := h.unique (hasDerivAt_const (0:ℝ) (choiceProb f π i))
  rw [← Finset.sum_apply, ← map_sum]
  have : ∑ j : Fin m, Pi.single j (1:ℝ) = (1 : Fin m → ℝ) :=
    Finset.univ_sum_single (fun _ : Fin m => (1:ℝ))
  rw [this, h0]

theorem split_sum {m : ℕ} (g : Fin m → ℝ) (p : Fin m → Prop) [DecidablePred p] :
    ∑ j, (if p j then g j else 0) = ∑ j, g j + ∑ j, (if ¬ p j then -g j else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : p j <;> simp [h]

theorem combin {m : ℕ} (D : Fin m → Fin m → ℝ) (hr : ∀ i, ∑ j, D i j = 0)
    (hc : ∀ j, ∑ i, D i j = 0) (hn : ∀ i j, i ≠ j → D i j < 0) (k l : Fin m)
    (hk : k.val + 1 < m) (hl : l.val + 1 < m) :
    0 < ∑ i : Fin m, ∑ j : Fin m, (if i ≤ k ∧ j ≤ l then D i j else 0) := by
  have hm : 0 < m := by omega
  let last : Fin m := ⟨m - 1, by omega⟩
  let zero : Fin m := ⟨0, hm⟩
  have hlastk : ¬ last ≤ k := by simp only [Fin.le_def, last]; omega
  have hlastl : ¬ last ≤ l := by simp only [Fin.le_def, last]; omega
  have hzk : zero ≤ k := by simp [Fin.le_def, zero]
  have hzl : zero ≤ l := by simp [Fin.le_def, zero]
  rcases le_or_gt k l with hkl | hkl
  · have e1 : ∀ i, ∑ j : Fin m, (if i ≤ k ∧ j ≤ l then D i j else 0)
        = ∑ j : Fin m, (if i ≤ k ∧ ¬ j ≤ l then -D i j else 0) := by
      intro i
      by_cases hi : i ≤ k
      · simp only [hi, true_and]
        rw [split_sum (D i) (fun j => j ≤ l), hr i, zero_add]
      · simp [hi]
    simp_rw [e1]
    have hnn : ∀ i j, 0 ≤ (if i ≤ k ∧ ¬ j ≤ l then -D i j else 0) := by
      intro i j
      split_ifs with h
      · have : i ≠ j := by
          intro e; subst e; exact h.2 (h.1.trans hkl)
        linarith [hn i j this]
      · rfl
    apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)
    refine ⟨zero, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos' (fun j _ => hnn zero j)
    refine ⟨last, Finset.mem_univ _, ?_⟩
    rw [if_pos ⟨hzk, hlastl⟩]
    have : zero ≠ last := fun e => hlastk (e ▸ hzk)
    linarith [hn zero last this]
  · rw [Finset.sum_comm]
    have e1 : ∀ j, ∑ i : Fin m, (if i ≤ k ∧ j ≤ l then D i j else 0)
        = ∑ i : Fin m, (if ¬ i ≤ k ∧ j ≤ l then -D i j else 0) := by
      intro j
      by_cases hj : j ≤ l
      · simp only [hj, and_true]
        rw [split_sum (fun i => D i j) (fun i => i ≤ k), hc j, zero_add]
      · simp [hj]
    simp_rw [e1]
    have hnn : ∀ j i, 0 ≤ (if ¬ i ≤ k ∧ j ≤ l then -D i j else 0) := by
      intro j i
      split_ifs with h
      · have : i ≠ j := by
          intro e; subst e; exact h.1 (h.2.trans hkl.le)
        linarith [hn i j this]
      · rfl
    apply Finset.sum_pos' (fun j _ => Finset.sum_nonneg fun i _ => hnn j i)
    refine ⟨zero, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos' (fun i _ => hnn zero i)
    refine ⟨last, Finset.mem_univ _, ?_⟩
    rw [if_pos ⟨hlastk, hzl⟩]
    have : last ≠ zero := fun e => hlastk (e ▸ hzk)
    linarith [hn last zero this]


theorem tie_null {m : ℕ} (a b : Fin m) (hab : a ≠ b) (c : ℝ) :
    volume {e : Fin m → ℝ | e a = e b + c} = 0 := by
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) a -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) b
  have hL : ∀ x, L x = x a - x b := fun x => rfl
  let p : Fin m → ℝ := c • Pi.single a 1
  have hp : L p = c := by simp [hL, p, hab.symm]
  let s : AffineSubspace ℝ (Fin m → ℝ) := AffineSubspace.mk' p (LinearMap.ker L)
  have hsub : {e : Fin m → ℝ | e a = e b + c} ⊆ s := by
    intro e he
    simp only [Set.mem_ofPred_eq] at he
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, hp, hL]
    linarith
  have hne : s ≠ ⊤ := by
    intro h
    have hq : p + Pi.single a 1 ∈ s := by rw [h]; exact AffineSubspace.mem_top _ _ _
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, add_sub_cancel_left, hL] at hq
    simp [hab.symm] at hq
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace _ s hne)

theorem meas_E {m : ℕ} (π : Fin m → ℝ) (i : Fin m) :
    MeasurableSet {e : Fin m → ℝ | ∀ j, j ≠ i → π j + e j < π i + e i} := by
  have : {e : Fin m → ℝ | ∀ j, j ≠ i → π j + e j < π i + e i}
      = ⋂ j, ⋂ (_ : j ≠ i), {e : Fin m → ℝ | π j + e j < π i + e i} := by
    ext e; simp
  rw [this]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_lt (by fun_prop) (by fun_prop)

theorem mu_univ {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) :
    (volume.withDensity f) Set.univ = 1 := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hf.2.2.2.1]

theorem sum_one {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (hm : Nonempty (Fin m)) :
    ∑ i, choiceProb f π i = 1 := by
  set μ := volume.withDensity f
  set E : Fin m → Set (Fin m → ℝ) := fun i => {e | ∀ j, j ≠ i → π j + e j < π i + e i}
  have hU : μ Set.univ = 1 := mu_univ f hf
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro i i' hii'
    refine Set.disjoint_left.2 fun e h1 h2 => ?_
    have := h1 i' (Ne.symm hii'); have := h2 i hii'; linarith
  have hunion : μ (⋃ i, E i) = ∑ i, μ (E i) := by
    rw [measure_iUnion hdisj (fun i => meas_E π i), tsum_fintype]
  have hcompl : μ (⋃ i, E i)ᶜ = 0 := by
    have hsub : (⋃ i, E i)ᶜ ⊆ ⋃ a, ⋃ b, ⋃ (_ : a ≠ b), {e : Fin m → ℝ | e a = e b + (π b - π a)} := by
      intro e he
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at he
      have hne : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty
      obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun k => π k + e k) hne
      have := he i
      simp only [E, Set.mem_ofPred_eq, not_forall, not_lt] at this
      obtain ⟨j, hji, hj⟩ := this
      have := hi j (Finset.mem_univ _)
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨j, i, hji, by linarith⟩
    refine measure_mono_null hsub ?_
    refine (measure_iUnion_null fun a => measure_iUnion_null fun b => measure_iUnion_null fun hab => ?_)
    exact withDensity_absolutelyContinuous _ _ (tie_null a b hab _)
  have hfull : μ (⋃ i, E i) = 1 := by
    apply le_antisymm (hU ▸ measure_mono (Set.subset_univ _))
    calc (1 : ℝ≥0∞) = μ Set.univ := hU.symm
      _ ≤ μ ((⋃ i, E i) ∪ (⋃ i, E i)ᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ (⋃ i, E i) + μ (⋃ i, E i)ᶜ := measure_union_le _ _
      _ = μ (⋃ i, E i) := by rw [hcompl, add_zero]
  have hfin : ∀ i, μ (E i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (by rw [hU]; exact ENNReal.one_ne_top) (measure_mono (Set.subset_univ _))
  unfold choiceProb
  change ∑ i, (μ (E i)).toReal = 1
  rw [← ENNReal.toReal_sum (fun i _ => hfin i), ← hunion, hfull, ENNReal.toReal_one]

theorem col_sum {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (j : Fin m) : ∑ i : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i = 0 := by
  have hm : Nonempty (Fin m) := ⟨j⟩
  have h : HasDerivAt (fun t : ℝ => ∑ i, choiceProb f (π + t • Pi.single j (1:ℝ)) i)
      (∑ i : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i) 0 :=
    HasDerivAt.fun_sum (fun i _ => line_deriv f hf π _ i)
  simp only [sum_one f hf _ hm] at h
  exact h.unique (hasDerivAt_const (0:ℝ) (1:ℝ))


theorem pfsa_apply {n : ℕ} (i : Fin (n+1)) (e : Fin (n+1) → ℝ) :
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i e = (e i, fun k => e (i.succAbove k)) := by
  simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]; rfl

theorem region_bound {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ≥0∞) (hfc : Continuous f)
    (hpos : ∀ e, 0 < f e) (hfin : ∀ e, f e ≠ ⊤) (π : Fin (n+1) → ℝ) (i j : Fin (n+1))
    (hij : i ≠ j) :
    ∃ c > 0, ∃ r > 0, ∀ t : ℝ, 0 < t → t < r → ∃ R : Set (Fin (n+1) → ℝ),
      R ⊆ {e | (∀ k, k ≠ i → π k + e k < π i + e i) ∧ π i + e i ≤ π j + t + e j} ∧
      ENNReal.ofReal (c * t) ≤ volume.withDensity f R := by
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
  set e0 : Fin (n+1) → ℝ := fun k => if k = i then 0 else if k = j then π i - π j
    else π i - π k - 1 with he0
  have e0i : e0 i = 0 := by simp [he0]
  have e0j : e0 j = π i - π j := by simp [he0, hij.symm]
  have e0k : ∀ k, k ≠ i → k ≠ j → e0 k = π i - π k - 1 := by
    intro k h1 h2; simp [he0, h1, h2]
  set δ := f e0 / 2 with hδ
  have hδpos : 0 < δ := ENNReal.half_pos (hpos e0).ne'
  have hδlt : δ < f e0 := ENNReal.half_lt_self (hpos e0).ne' (hfin e0)
  have hδfin : δ ≠ ⊤ := ne_top_of_lt hδlt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 ((hfc.tendsto e0).eventually (lt_mem_nhds hδlt))
  set r := min (ε / 2) (1 / 4) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hrε : r ≤ ε / 2 := min_le_left _ _
  have hr4 : r ≤ 1 / 4 := min_le_right _ _
  set B : Set (Fin n → ℝ) := Set.univ.pi fun k' => Set.Ioo (e0 (i.succAbove k') - r) (e0 (i.succAbove k') + r)
    with hB
  have hBm : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  set V := (volume : Measure (Fin n → ℝ)) B with hV
  have hVeq : V = ∏ _k' : Fin n, ENNReal.ofReal (2 * r) := by
    rw [hV, hB, Real.volume_pi_Ioo]; congr 1; ext k'; congr 1; ring
  have hVpos : V ≠ 0 := by
    rw [hVeq, Finset.prod_ne_zero_iff]; intro _ _; simp; linarith
  have hVfin : V ≠ ⊤ := by rw [hVeq]; exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  refine ⟨(δ * V).toReal, ENNReal.toReal_pos (mul_ne_zero hδpos.ne' hVpos)
    (ENNReal.mul_ne_top hδfin hVfin), r, hr0, fun t ht htr => ?_⟩
  set W : Set (ℝ × (Fin n → ℝ)) := {p | p.2 ∈ B ∧ p.1 ∈ Set.Ioc (π j + p.2 j' - π i) (π j + p.2 j' - π i + t)}
    with hW
  have hWm : MeasurableSet W := by
    have : W = Prod.snd ⁻¹' B ∩ ({p : ℝ × (Fin n → ℝ) | π j + p.2 j' - π i < p.1} ∩
        {p : ℝ × (Fin n → ℝ) | p.1 ≤ π j + p.2 j' - π i + t}) := by
      ext p; simp [hW]
    rw [this]
    refine (measurable_snd hBm).inter ?_
    exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (by fun_prop) (by fun_prop))
  set R := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' W with hRdef
  have memR : ∀ e ∈ R, (∀ k', e (i.succAbove k') ∈ Set.Ioo (e0 (i.succAbove k') - r) (e0 (i.succAbove k') + r))
      ∧ π j + e j - π i < e i ∧ e i ≤ π j + e j - π i + t := by
    intro e he
    simp only [hRdef, Set.mem_preimage, pfsa_apply, hW, hB, Set.mem_ofPred_eq, Set.mem_pi,
      Set.mem_univ, true_implies, Set.mem_Ioc] at he
    rw [hj'] at he
    exact ⟨he.1, he.2.1, he.2.2⟩
  -- bounds on e i
  have bnd : ∀ e ∈ R, -r < e i ∧ e i < 2 * r := by
    intro e he
    obtain ⟨h1, h2, h3⟩ := memR e he
    have := h1 j'
    rw [hj', e0j] at this
    constructor <;> [linarith [this.1]; linarith [this.2]]
  refine ⟨R, ?_, ?_⟩
  · intro e he
    obtain ⟨h1, h2, h3⟩ := memR e he
    obtain ⟨b1, b2⟩ := bnd e he
    refine ⟨fun k hk => ?_, by linarith⟩
    obtain ⟨k', rfl⟩ | h := (Fin.eq_self_or_eq_succAbove i k).symm.imp id id
    · by_cases hkj : i.succAbove k' = j
      · rw [hkj]; linarith
      · have := (h1 k').2
        rw [e0k _ hk hkj] at this
        linarith
    · exact absurd h hk
  · -- measure
    have hvolR : volume R = ENNReal.ofReal t * V := by
      change (Measure.pi fun _ => volume) _ = _
      rw [hRdef, (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) i).measure_preimage
        hWm.nullMeasurableSet, Measure.prod_apply_symm hWm]
      have : ∀ y : Fin n → ℝ, volume ((fun x : ℝ => (x, y)) ⁻¹' W) = B.indicator (fun _ => ENNReal.ofReal t) y := by
        intro y
        by_cases hy : y ∈ B
        · rw [Set.indicator_of_mem hy]
          have : (fun x : ℝ => (x, y)) ⁻¹' W = Set.Ioc (π j + y j' - π i) (π j + y j' - π i + t) := by
            ext x; simp [hW, hy]
          rw [this, Real.volume_Ioc]; congr 1; ring
        · rw [Set.indicator_of_notMem hy]
          have : (fun x : ℝ => (x, y)) ⁻¹' W = ∅ := by
            ext x; simp [hW, hy]
          rw [this, measure_empty]
      simp_rw [this]
      rw [lintegral_indicator_const hBm]
      rfl
    have hRm : MeasurableSet R := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).measurable hWm
    have hlow : δ * (ENNReal.ofReal t * V) ≤ volume.withDensity f R := by
      rw [withDensity_apply _ hRm, ← hvolR, ← setLIntegral_const]
      apply setLIntegral_mono hfc.measurable
      intro e he
      apply le_of_lt
      apply hball
      rw [dist_pi_lt_iff hε]
      intro k
      rw [Real.dist_eq]
      obtain ⟨b1, b2⟩ := bnd e he
      obtain ⟨h1, -, -⟩ := memR e he
      rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨k', rfl⟩
      · rw [e0i, sub_zero, abs_lt]; constructor <;> linarith
      · have := h1 k'
        rw [abs_lt]; constructor <;> linarith [this.1, this.2]
    calc ENNReal.ofReal ((δ * V).toReal * t) = δ * (ENNReal.ofReal t * V) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal
            (ENNReal.mul_ne_top hδfin hVfin)]
          ring
      _ ≤ _ := hlow

theorem offdiag_neg {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (i j : Fin m) (hij : i ≠ j) : fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i < 0 := by
  have hd := line_deriv f hf π (Pi.single j (1:ℝ)) i
  set d := fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i
  cases m with
  | zero => exact i.elim0
  | succ n =>
  obtain ⟨c, hc, r, hr, H⟩ := region_bound f hf.1 hf.2.1 hf.2.2.1 π i j hij
  set g := fun t : ℝ => choiceProb f (π + t • Pi.single j (1:ℝ)) i
  have key : ∀ t, 0 < t → t < r → g t ≤ g 0 - c * t := by
    intro t ht htr
    obtain ⟨R, hRsub, hRlow⟩ := H t ht htr
    set μ := volume.withDensity f
    set E := {e : Fin (n+1) → ℝ | ∀ k, k ≠ i → π k + e k < π i + e i}
    set π' := π + t • Pi.single j (1:ℝ)
    set E' := {e : Fin (n+1) → ℝ | ∀ k, k ≠ i → π' k + e k < π' i + e i}
    have hπ'i : π' i = π i := by simp [π', hij]
    have hπ'j : π' j = π j + t := by simp [π']
    have hπ'le : ∀ k, π k ≤ π' k := by
      intro k; simp only [π', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : (0:ℝ) ≤ (Pi.single j (1:ℝ) : Fin (n+1) → ℝ) k := by
        by_cases h : k = j
        · subst h; simp
        · simp [h]
      nlinarith
    have hsub : E' ⊆ E := by
      intro e he k hk
      have := he k hk; have := hπ'le k; rw [hπ'i] at *; linarith
    have hRdiff : R ⊆ E \ E' := by
      intro e he
      obtain ⟨h1, h2⟩ := hRsub he
      refine ⟨h1, fun h' => ?_⟩
      have := h' j hij.symm
      rw [hπ'i, hπ'j] at this
      linarith
    have hU : μ Set.univ = 1 := mu_univ f hf
    have hfin : ∀ s, μ s ≠ ⊤ := fun s =>
      ne_top_of_le_ne_top (by rw [hU]; exact ENNReal.one_ne_top) (measure_mono (Set.subset_univ _))
    have hsplit : μ E' + μ (E \ E') = μ E := by
      rw [measure_add_sdiff (meas_E π' i).nullMeasurableSet, Set.union_eq_right.2 hsub]
    have hg0 : g 0 = (μ E).toReal := by simp [g, choiceProb, μ, E]
    have hgt : g t = (μ E').toReal := rfl
    rw [hg0, hgt, ← hsplit, ENNReal.toReal_add (hfin _) (hfin _)]
    have : c * t ≤ (μ (E \ E')).toReal := by
      have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (hfin _)).2
        (hRlow.trans (measure_mono hRdiff))
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    linarith
  have hlim := hd.tendsto_slope_zero_right
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t⁻¹ • (g (0 + t) - g 0) ≤ -c := by
    have : Set.Ioo (0:ℝ) r ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT hr
    filter_upwards [this] with t ht
    obtain ⟨ht0, htr⟩ := ht
    rw [zero_add, smul_eq_mul, inv_mul_le_iff₀ ht0]
    have := key t ht0 htr
    nlinarith
  have := le_of_tendsto hlim hev
  linarith

end SF90

open MeasureTheory
open scoped ENNReal

namespace TC90
open StochFictPlay.Supermodular

/-- INTERFACE (proved elsewhere; do not prove here): row sums of the Jacobian vanish. -/
theorem row_sum {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (i : Fin m) : ∑ j : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i = 0 :=
  SF90.row_sum f hf π i

/-- INTERFACE: column sums of the Jacobian vanish. -/
theorem col_sum {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (j : Fin m) : ∑ i : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i = 0 :=
  SF90.col_sum f hf π j

/-- INTERFACE: off-diagonal partials are strictly negative. -/
theorem offdiag_neg {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (i j : Fin m) (hij : i ≠ j) : fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i < 0 :=
  SF90.offdiag_neg f hf π i j hij


lemma tailMass_add_single {m : ℕ} (w : Fin (m - 1) → ℝ) (j : Fin (m - 1)) (t : ℝ) (k : ℕ) :
    tailMass (w + t • Pi.single j (1 : ℝ)) k
      = tailMass w k + t * (if k = j.val + 1 then 1 else 0) := by
  unfold tailMass
  by_cases h0 : k = 0
  · simp [h0]
  · by_cases h1 : k - 1 < m - 1
    · simp only [h0, h1, if_false, dif_pos, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply, Fin.ext_iff]
      by_cases h2 : k = j.val + 1
      · simp [h2]
      · have : ¬ (k - 1 = j.val) := by omega
        simp [h2, this]
    · have : ¬ (k = j.val + 1) := by have := j.2; omega
      simp [h0, h1, this]

/-- the direction of `Tinv` for a unit perturbation of coordinate `j` -/
def wv {m : ℕ} (j : Fin (m - 1)) (k : Fin m) : ℝ :=
  (if k.val = j.val + 1 then 1 else 0) - (if k.val = j.val then 1 else 0)

lemma Tinv_add_single {m : ℕ} (w : Fin (m - 1) → ℝ) (j : Fin (m - 1)) (t : ℝ) (k : Fin m) :
    Tinv (w + t • Pi.single j (1 : ℝ)) k = Tinv w k + t * wv j k := by
  unfold Tinv wv
  rw [tailMass_add_single, tailMass_add_single]
  have : (k.val + 1 = j.val + 1) ↔ k.val = j.val := by omega
  simp only [this]
  ring

variable {p : ℕ} {n : Fin p → ℕ}

lemma line_ne (v : Coord n) (β : Fin p) (e : Fin (n β - 1) → ℝ) (t : ℝ) (γ : Fin p)
    (h : γ ≠ β) : (v + t • (Pi.single β e : Coord n)) γ = v γ := by
  simp [Pi.single_eq_of_ne h]

lemma TinvMap_line_ne (v : Coord n) (β : Fin p) (e : Fin (n β - 1) → ℝ) (t : ℝ) (γ : Fin p)
    (h : γ ≠ β) : TinvMap (v + t • (Pi.single β e : Coord n)) γ = TinvMap v γ := by
  simp only [TinvMap, line_ne v β e t γ h]

lemma TinvMap_line_eq (v : Coord n) (β : Fin p) (j : Fin (n β - 1)) (t : ℝ) (k : Fin (n β)) :
    TinvMap (v + t • (Pi.single β (Pi.single j (1 : ℝ)) : Coord n)) β k = TinvMap v β k + t * wv j k := by
  have : (v + t • (Pi.single β (Pi.single j (1 : ℝ)) : Coord n)) β = v β + t • Pi.single j (1 : ℝ) := by
    simp
  simp only [TinvMap, this, Tinv_add_single]

/-- the product of the opponents other than `β` -/
noncomputable def Pw (α β : Fin p) (x : Mixed n) (s : Profile n) : ℝ :=
  ∏ γ ∈ (Finset.univ.erase α).erase β, x γ (s γ)

noncomputable def dvec (u : (α : Fin p) → Profile n → ℝ) (v : Coord n) (α β : Fin p)
    (j : Fin (n β - 1)) (k : Fin (n α)) : ℝ :=
  ∑ s : Profile n, if s α = k then u α s * (wv j (s β) * Pw α β (TinvMap v) s) else 0

lemma payoff_line (u : (α : Fin p) → Profile n → ℝ) (v : Coord n) (α β : Fin p) (hαβ : α ≠ β)
    (j : Fin (n β - 1)) (t : ℝ) (k : Fin (n α)) :
    payoffVec u (TinvMap (v + t • (Pi.single β (Pi.single j (1 : ℝ)) : Coord n))) α k
      = payoffVec u (TinvMap v) α k + t * dvec u v α β j k := by
  unfold payoffVec dvec
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · have hβ : β ∈ Finset.univ.erase α := by simp [Ne.symm hαβ]
    rw [← Finset.mul_prod_erase _ _ hβ, ← Finset.mul_prod_erase _ _ hβ]
    have hP : ∏ γ ∈ (Finset.univ.erase α).erase β,
        TinvMap (v + t • (Pi.single β (Pi.single j (1 : ℝ)) : Coord n)) γ (s γ)
        = Pw α β (TinvMap v) s := by
      unfold Pw
      refine Finset.prod_congr rfl fun γ hγ => ?_
      rw [TinvMap_line_ne v β _ t γ (Finset.ne_of_mem_erase hγ)]
    rw [hP, TinvMap_line_eq]
    unfold Pw
    ring
  · simp

lemma payoff_line_same (u : (α : Fin p) → Profile n → ℝ) (v : Coord n) (α : Fin p)
    (e : Fin (n α - 1) → ℝ) (t : ℝ) :
    payoffVec u (TinvMap (v + t • (Pi.single α e : Coord n))) α = payoffVec u (TinvMap v) α := by
  funext k
  unfold payoffVec
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · congr 1
    refine Finset.prod_congr rfl fun γ hγ => ?_
    rw [TinvMap_line_ne v α _ t γ (Finset.ne_of_mem_erase hγ)]
  · rfl

end TC90

open MeasureTheory
open scoped ENNReal

namespace TC90
open StochFictPlay.Supermodular

lemma Tinv_nonneg {m : ℕ} (v : Fin (m - 1) → ℝ)
    (hv : (∀ i, v i ≤ 1 ∧ 0 ≤ v i) ∧ Antitone v) (k : Fin m) : 0 ≤ Tinv v k := by
  unfold Tinv tailMass
  by_cases h0 : k.val = 0
  · simp only [h0, if_true, Nat.zero_add, one_ne_zero, if_false, Nat.sub_self]
    split_ifs with h
    · linarith [(hv.1 ⟨0, h⟩).1]
    · norm_num
  · simp only [h0, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    split_ifs with h1 h2 h2
    · have := hv.2 (show (⟨k.val - 1, h1⟩ : Fin (m - 1)) ≤ ⟨k.val, h2⟩ from by
        simp [Fin.le_def])
      linarith
    · linarith [(hv.1 ⟨k.val - 1, h1⟩).2]
    · omega
    · norm_num

lemma Tinv_sum {m : ℕ} (hm : 1 ≤ m) (v : Fin (m - 1) → ℝ) : ∑ k : Fin m, Tinv v k = 1 := by
  unfold Tinv
  rw [Fin.sum_univ_eq_sum_range (fun k => tailMass v k - tailMass v (k + 1)) m,
    Finset.sum_range_sub']
  unfold tailMass
  have : m ≠ 0 := by omega
  simp [this]

lemma Tinv_exists_pos {m : ℕ} (hm : 1 ≤ m) (v : Fin (m - 1) → ℝ) : ∃ k, 0 < Tinv v k := by
  by_contra h
  push Not at h
  have := Tinv_sum hm v
  have : ∑ k : Fin m, Tinv v k ≤ 0 := Finset.sum_nonpos fun k _ => h k
  linarith

variable {p : ℕ} {n : Fin p → ℕ}

/-- the involution used for reindexing -/
def swp (α β : Fin p) (a a0 : Fin (n α)) (b b0 : Fin (n β)) (s : Profile n) : Profile n :=
  Function.update (Function.update s α (Equiv.swap a a0 (s α))) β (Equiv.swap b b0 (s β))

lemma swp_α {α β : Fin p} (h : α ≠ β) (a a0 : Fin (n α)) (b b0 : Fin (n β)) (s : Profile n) :
    swp α β a a0 b b0 s α = Equiv.swap a a0 (s α) := by
  simp [swp, Function.update_of_ne h]

lemma swp_β {α β : Fin p} (a a0 : Fin (n α)) (b b0 : Fin (n β)) (s : Profile n) :
    swp α β a a0 b b0 s β = Equiv.swap b b0 (s β) := by
  simp [swp]

lemma swp_other {α β : Fin p} (a a0 : Fin (n α)) (b b0 : Fin (n β)) (s : Profile n) (γ : Fin p)
    (h1 : γ ≠ α) (h2 : γ ≠ β) : swp α β a a0 b b0 s γ = s γ := by
  simp [swp, Function.update_of_ne h1, Function.update_of_ne h2]

lemma swp_invol {α β : Fin p} (h : α ≠ β) (a a0 : Fin (n α)) (b b0 : Fin (n β)) :
    Function.Involutive (swp α β a a0 b b0) := by
  intro s
  funext γ
  by_cases h1 : γ = α
  · subst h1; rw [swp_α h, swp_α h]; simp
  · by_cases h2 : γ = β
    · subst h2; rw [swp_β, swp_β]; simp
    · rw [swp_other _ _ _ _ _ γ h1 h2, swp_other _ _ _ _ _ γ h1 h2]

lemma sum_reindex {α β : Fin p} (h : α ≠ β) (a a0 : Fin (n α)) (b b0 : Fin (n β))
    (G : Profile n → ℝ) :
    ∑ s : Profile n, (if s α = a ∧ s β = b then G s else 0)
      = ∑ s : Profile n, (if s α = a0 ∧ s β = b0 then G (swp α β a a0 b b0 s) else 0) := by
  let e : Equiv.Perm (Profile n) := Function.Involutive.toPerm _ (swp_invol h a a0 b b0)
  rw [← Equiv.sum_comp e (fun s => if s α = a0 ∧ s β = b0 then G (swp α β a a0 b b0 s) else 0)]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [e, Function.Involutive.coe_toPerm, swp_α h, swp_β, swp_invol h a a0 b b0 s,
    Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]


lemma dvec_eq (u : (α : Fin p) → Profile n → ℝ) (v : Coord n) {α β : Fin p} (h : α ≠ β)
    (j : Fin (n β - 1)) (k : Fin (n α)) (a0 : Fin (n α)) (b0 : Fin (n β)) :
    dvec u v α β j k = ∑ s : Profile n, if s α = a0 ∧ s β = b0 then
      Pw α β (TinvMap v) s * (u α (Function.update (Function.update s α k) β ⟨j.val + 1, by omega⟩)
        - u α (Function.update (Function.update s α k) β ⟨j.val, by omega⟩)) else 0 := by
  set jS : Fin (n β) := ⟨j.val + 1, by omega⟩
  set jC : Fin (n β) := ⟨j.val, by omega⟩
  have step : ∀ s : Profile n,
      (if s α = k then u α s * (wv j (s β) * Pw α β (TinvMap v) s) else 0)
        = (if s α = k ∧ s β = jS then u α s * Pw α β (TinvMap v) s else 0)
          - (if s α = k ∧ s β = jC then u α s * Pw α β (TinvMap v) s else 0) := by
    intro s
    have e1 : (s β).val = j.val + 1 ↔ s β = jS := by simp [jS, Fin.ext_iff]
    have e2 : (s β).val = j.val ↔ s β = jC := by simp [jC, Fin.ext_iff]
    unfold wv
    by_cases hk : s α = k
    · by_cases h1 : s β = jS
      · rw [h1]; simp [hk, jS, jC, Fin.ext_iff]
      · by_cases h2 : s β = jC
        · rw [h2]; simp [hk, jS, jC, Fin.ext_iff]
        · simp [hk, h1, h2, e1, e2]
    · simp [hk]
  unfold dvec
  rw [Finset.sum_congr rfl fun s _ => step s, Finset.sum_sub_distrib,
    sum_reindex h k a0 jS b0, sum_reindex h k a0 jC b0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hc : s α = a0 ∧ s β = b0
  · have hP : ∀ b : Fin (n β), Pw α β (TinvMap v) (swp α β k a0 b b0 s) = Pw α β (TinvMap v) s := by
      intro b
      unfold Pw
      refine Finset.prod_congr rfl fun γ hγ => ?_
      have h2 := Finset.ne_of_mem_erase hγ
      have h1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hγ)
      rw [swp_other _ _ _ _ _ γ h1 h2]
    have hs : ∀ b : Fin (n β), swp α β k a0 b b0 s = Function.update (Function.update s α k) β b := by
      intro b
      unfold swp
      rw [hc.1, hc.2, Equiv.swap_apply_right, Equiv.swap_apply_right]
    simp only [hc, and_self, if_true]
    rw [hP jS, hP jC, hs, hs]
    ring
  · simp [hc]

lemma dvec_strictMono (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (hn : ∀ α, 1 ≤ n α) (v : Coord n) (hv : v ∈ TSigma n) {α β : Fin p} (h : α ≠ β)
    (j : Fin (n β - 1)) : StrictMono (dvec u v α β j) := by
  have hpos : ∀ γ, ∃ k, 0 < TinvMap v γ k := fun γ => Tinv_exists_pos (hn γ) (v γ)
  choose c hc using hpos
  intro k k' hkk'
  rw [dvec_eq u v h j k (c α) (c β), dvec_eq u v h j k' (c α) (c β), ← sub_pos,
    ← Finset.sum_sub_distrib]
  have hP : ∀ s, 0 ≤ Pw α β (TinvMap v) s := fun s =>
    Finset.prod_nonneg fun γ _ => Tinv_nonneg (v γ) (hv γ) (s γ)
  have hΔ : ∀ s : Profile n, 0 <
      (u α (Function.update (Function.update s α k') β ⟨j.val + 1, by omega⟩)
        - u α (Function.update (Function.update s α k') β ⟨j.val, by omega⟩))
      - (u α (Function.update (Function.update s α k) β ⟨j.val + 1, by omega⟩)
        - u α (Function.update (Function.update s α k) β ⟨j.val, by omega⟩)) := by
    intro s
    have := hu α β h s k' k hkk' (show (⟨j.val, by omega⟩ : Fin (n β)) < ⟨j.val + 1, by omega⟩ from by
      simp [Fin.lt_def])
    simp only at this
    linarith
  apply Finset.sum_pos'
  · intro s _
    split_ifs
    · rw [← mul_sub]; exact mul_nonneg (hP s) (by linarith [hΔ s])
    · simp
  · refine ⟨c, Finset.mem_univ _, ?_⟩
    simp only [and_self, if_true]
    rw [← mul_sub]
    refine mul_pos ?_ (by linarith [hΔ c])
    exact Finset.prod_pos fun γ _ => hc γ

end TC90

namespace TC90

lemma upper_pos {m : ℕ} (D : Fin m → Fin m → ℝ) (hrow : ∀ a, ∑ k, D k a = 0)
    (hcol : ∀ k, ∑ a, D k a = 0) (hoff : ∀ k a, k ≠ a → D k a < 0) (d : Fin m → ℝ)
    (hd : StrictMono d) (i : ℕ) (hi : i + 1 < m) :
    0 < ∑ a : Fin m, if i < a.val then ∑ k, d k * D k a else 0 := by
  set h : Fin m → ℝ := fun k => ∑ a : Fin m, if i < a.val then D k a else 0 with hh
  have s1 : (∑ a : Fin m, if i < a.val then ∑ k, d k * D k a else 0) = ∑ k, d k * h k := by
    have : ∀ a : Fin m, (if i < a.val then ∑ k, d k * D k a else 0)
        = ∑ k, (if i < a.val then d k * D k a else 0) := by
      intro a; split_ifs <;> simp
    rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hh, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  have s2 : ∑ k, h k = 0 := by
    rw [hh, Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs
    · exact hrow a
    · simp
  set c := d ⟨i, by omega⟩ with hc
  have s3 : ∑ k, d k * h k = ∑ k, (d k - c) * h k := by
    have : ∑ k, (d k - c) * h k = ∑ k, d k * h k - c * ∑ k, h k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, s2]; ring
  have hsplit : ∀ k, h k = - ∑ a : Fin m, if i < a.val then 0 else D k a := by
    intro k
    have : ∑ a : Fin m, D k a = h k + ∑ a : Fin m, if i < a.val then 0 else D k a := by
      rw [hh, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
    linarith [hcol k]
  have hpos : ∀ k : Fin m, i < k.val → 0 < h k := by
    intro k hk
    rw [hsplit k, neg_pos]
    have : (∑ a : Fin m, if i < a.val then 0 else D k a) < ∑ a : Fin m, (0 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro a _
        split_ifs with ha
        · exact le_rfl
        · exact (hoff k a (by intro e; subst e; omega)).le
      · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
        simp only [Nat.not_lt_zero, if_false]
        exact hoff k _ (by intro e; rw [Fin.ext_iff] at e; simp at e; omega)
    simpa using this
  have hneg : ∀ k : Fin m, k.val ≤ i → h k ≤ 0 := by
    intro k hk
    rw [hh]
    apply Finset.sum_nonpos
    intro a _
    split_ifs with ha
    · exact (hoff k a (by intro e; subst e; omega)).le
    · exact le_rfl
  rw [s1, s3]
  apply Finset.sum_pos'
  · intro k _
    by_cases hk : i < k.val
    · have : c < d k := hd (show (⟨i, by omega⟩ : Fin m) < k from by simp [Fin.lt_def]; omega)
      exact mul_nonneg (by linarith) (hpos k hk).le
    · have : d k ≤ c := hd.monotone (show k ≤ (⟨i, by omega⟩ : Fin m) from by
        simp [Fin.le_def]; omega)
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (hneg k (by omega))
  · refine ⟨⟨i + 1, hi⟩, Finset.mem_univ _, ?_⟩
    have : c < d ⟨i + 1, hi⟩ := hd (show (⟨i, by omega⟩ : Fin m) < ⟨i + 1, hi⟩ from by
      simp [Fin.lt_def])
    exact mul_pos (by linarith) (hpos _ (by simp))

end TC90

open MeasureTheory
open scoped ENNReal

namespace TC90
open StochFictPlay.Supermodular

variable {p : ℕ} {n : Fin p → ℕ}

lemma tailMass_diff (β : Fin p) (k : ℕ) :
    Differentiable ℝ (fun v : Coord n => tailMass (v β) k) := by
  unfold tailMass
  split_ifs with h1 h2
  · exact differentiable_const _
  · fun_prop
  · exact differentiable_const _

lemma payoff_diff (u : (α : Fin p) → Profile n → ℝ) (α : Fin p) :
    Differentiable ℝ (fun v : Coord n => payoffVec u (TinvMap v) α) := by
  rw [differentiable_pi]
  intro k
  unfold payoffVec
  apply Differentiable.fun_sum
  intro s _
  by_cases hs : s α = k
  · simp only [hs, if_true]
    apply Differentiable.const_mul
    intro w
    have hd : ∀ γ ∈ Finset.univ.erase α,
        Differentiable ℝ (fun v : Coord n => TinvMap v γ (s γ)) := by
      intro γ _
      unfold TinvMap Tinv
      exact (tailMass_diff γ _).sub (tailMass_diff γ _)
    exact (HasFDerivAt.finsetProd (x := w) fun γ hγ => ((hd γ hγ) w).hasFDerivAt).differentiableAt
  · simp only [hs, if_false]
    exact differentiable_const _

lemma gField_diff (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) : Differentiable ℝ (gField f u) := by
  rw [differentiable_pi]
  intro α
  rw [differentiable_pi]
  intro i
  show Differentiable ℝ (fun v : Coord n =>
    Tco (choiceProb (f α) (payoffVec u (TinvMap v) α)) i - v α i)
  apply Differentiable.sub
  · unfold Tco
    apply Differentiable.fun_sum
    intro a _
    by_cases ha : i.val < a.val
    · simp only [ha, if_true]
      have := ((hf α).2.2.2.2.differentiable one_ne_zero).comp (payoff_diff u α)
      exact differentiable_pi.1 this a
    · simp only [ha, if_false]
      exact differentiable_const _
  · fun_prop

lemma partial_of_line {g : Coord n → Coord n} (v E : Coord n) (hg : DifferentiableAt ℝ g v)
    (α : Fin p) (i : Fin (n α - 1)) (D : ℝ)
    (hD : HasDerivAt (fun t : ℝ => g (v + t • E) α i) D 0) : fderiv ℝ g v E α i = D := by
  have h1 : HasDerivAt (fun t : ℝ => v + t • E) E 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const E).const_add v
  have h2 := hg.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
  have h3 := (hasDerivAt_pi.1 ((hasDerivAt_pi.1 h2) α)) i
  exact h3.unique hD


lemma partial_pos_ne (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u) (hn : ∀ α, 1 ≤ n α)
    (v : Coord n) (hv : v ∈ TSigma n) {α β : Fin p} (h : α ≠ β)
    (i : Fin (n α - 1)) (j : Fin (n β - 1)) :
    0 < partialDeriv (gField f u) v ⟨α, i⟩ ⟨β, j⟩ := by
  set E : Coord n := Pi.single β (Pi.single j (1 : ℝ)) with hE
  set π0 := payoffVec u (TinvMap v) α with hπ0
  set d := dvec u v α β j with hd
  set C := choiceProb (f α) with hC
  have hCd : Differentiable ℝ C := (hf α).2.2.2.2.differentiable one_ne_zero
  have hline : ∀ t : ℝ, gField f u (v + t • E) α i = Tco (C (π0 + t • d)) i - v α i := by
    intro t
    have h1 : payoffVec u (TinvMap (v + t • E)) α = π0 + t • d := by
      funext k; rw [payoff_line u v α β h j t k]; simp [π0, d]
    have h2 : (v + t • E) α = v α := line_ne v β _ t α h
    show Tco (choiceProb (f α) (payoffVec u (TinvMap (v + t • E)) α)) i - (v + t • E) α i = _
    rw [h1, h2]
  have hD : HasDerivAt (fun t : ℝ => gField f u (v + t • E) α i)
      (∑ a : Fin (n α), if i.val < a.val then fderiv ℝ C π0 d a else 0) 0 := by
    simp only [hline]
    have hc : HasDerivAt (fun t : ℝ => C (π0 + t • d)) (fderiv ℝ C π0 d) 0 :=
      (hCd _).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
        (by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add π0) (by simp)
    unfold Tco
    apply HasDerivAt.sub_const
    apply HasDerivAt.fun_sum
    intro a _
    by_cases ha : i.val < a.val
    · simp only [ha, if_true]; exact hasDerivAt_pi.1 hc a
    · simp only [ha, if_false]; exact hasDerivAt_const _ _
  unfold partialDeriv
  rw [partial_of_line v E ((gField_diff f hf u) v) α i _ hD]
  have hlin : ∀ a, fderiv ℝ C π0 d a = ∑ k, d k * fderiv ℝ C π0 (Pi.single k 1) a := by
    intro a
    have : d = ∑ k, d k • (Pi.single k (1 : ℝ) : Fin (n α) → ℝ) := by
      funext k'; simp [Pi.single_apply]
    conv_lhs => rw [this]
    simp [map_sum, map_smul]
  simp only [hlin]
  exact upper_pos (fun k a => fderiv ℝ C π0 (Pi.single k 1) a) (fun a => row_sum _ (hf α) π0 a)
    (fun k => col_sum _ (hf α) π0 k) (fun k a hka => offdiag_neg _ (hf α) π0 a k (Ne.symm hka))
    d (dvec_strictMono u hu hn v hv h j) i.val (by omega)

lemma partial_same (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (v : Coord n) (α : Fin p)
    (i j : Fin (n α - 1)) (hij : i ≠ j) :
    partialDeriv (gField f u) v ⟨α, i⟩ ⟨α, j⟩ = 0 := by
  set E : Coord n := Pi.single α (Pi.single j (1 : ℝ)) with hE
  have hline : ∀ t : ℝ, gField f u (v + t • E) α i =
      Tco (choiceProb (f α) (payoffVec u (TinvMap v) α)) i - v α i := by
    intro t
    show Tco (choiceProb (f α) (payoffVec u (TinvMap (v + t • E)) α)) i - (v + t • E) α i = _
    rw [payoff_line_same]
    simp [E, hij]
  have hD : HasDerivAt (fun t : ℝ => gField f u (v + t • E) α i) 0 0 := by
    simp only [hline]
    exact hasDerivAt_const _ _
  unfold partialDeriv
  exact partial_of_line v E ((gField_diff f hf u) v) α i _ hD

end TC90

namespace TC90
open StochFictPlay.Supermodular

theorem main_thm {p : ℕ} (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α)) :
    IsCooperative (gField f u) (TSigma n) ∧
      ((∃ α β : Fin p, α ≠ β ∧ 2 ≤ n α ∧ 2 ≤ n β) → IsIrreducible (gField f u) (TSigma n)) := by
  constructor
  · intro v hv a b hab
    obtain ⟨α, i⟩ := a
    obtain ⟨β, j⟩ := b
    by_cases h : α = β
    · subst h
      have hij : i ≠ j := by rintro rfl; exact hab rfl
      rw [partial_same f hf u v α i j hij]
    · exact (partial_pos_ne f hf u hu hn v hv h i j).le
  · rintro ⟨α, β, hαβ, hα, hβ⟩ I ⟨a0, ha0⟩ ⟨b0, hb0⟩
    have key : ∃ a ∈ I, ∃ b ∉ I, a.1 ≠ b.1 := by
      by_cases h : a0.1 = b0.1
      · have : ∃ c : Comp n, c.1 ≠ a0.1 := by
          by_cases hα' : α = a0.1
          · exact ⟨⟨β, ⟨0, by omega⟩⟩, by rw [← hα']; exact Ne.symm hαβ⟩
          · exact ⟨⟨α, ⟨0, by omega⟩⟩, hα'⟩
        obtain ⟨c, hc⟩ := this
        by_cases hcI : c ∈ I
        · exact ⟨c, hcI, b0, hb0, by rw [← h]; exact hc⟩
        · exact ⟨a0, ha0, c, hcI, Ne.symm hc⟩
      · exact ⟨a0, ha0, b0, hb0, h⟩
    obtain ⟨⟨α', i⟩, ha, ⟨β', j⟩, hb, hne⟩ := key
    exact ⟨_, ha, _, hb, fun v hv => (partial_pos_ne f hf u hu hn v hv hne i j).ne'⟩

end TC90

open StochFictPlay.Supermodular in
theorem solution {p : ℕ} (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α)) :
    IsCooperative (gField f u) (TSigma n) ∧
      ((∃ α β : Fin p, α ≠ β ∧ 2 ≤ n α ∧ 2 ≤ n β) → IsIrreducible (gField f u) (TSigma n)) :=
  TC90.main_thm n hn u hu f hf
