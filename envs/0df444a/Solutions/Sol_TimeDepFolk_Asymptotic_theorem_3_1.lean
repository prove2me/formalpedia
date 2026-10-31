-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:06:19.229504+00:00
-- url     : https://prove2.me/submissions/d0dbb071-1e60-4cf0-913d-f7380231360b

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model
import Theorems.Thm_TimeDepFolk_Asymptotic_interior_mem_eqPayoffs

set_option linter.unusedSectionVars false

namespace TDFAux

open TimeDepFolk.Asymptotic Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

theorem histProb_nonneg (σ : Profile A) {T : ℕ} (h : History A T) : 0 ≤ histProb σ h := by
  unfold histProb
  exact Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun i _ => ((σ i).act_mem _ _).1 _

theorem take_snoc_castSucc {T : ℕ} (h : History A T) (a : ∀ i, A i) (r : Fin T) :
    History.take (Fin.snoc h a : History A (T + 1)) r.castSucc (Nat.le_of_lt r.castSucc.isLt) =
      h.take r (Nat.le_of_lt r.isLt) := by
  funext q
  simp only [History.take]
  have : (Fin.castLE (Nat.le_of_lt r.castSucc.isLt) q : Fin (T + 1)) =
      (Fin.castLE (Nat.le_of_lt r.isLt) q).castSucc := by ext; simp
  rw [this, Fin.snoc_castSucc]

theorem take_snoc_last {T : ℕ} (h : History A T) (a : ∀ i, A i) :
    History.take (Fin.snoc h a : History A (T + 1)) (Fin.last T) (Nat.le_of_lt (Fin.last T).isLt) = h := by
  funext q
  simp only [History.take]
  have : (Fin.castLE (Nat.le_of_lt (Fin.last T).isLt) q : Fin (T + 1)) = q.castSucc := by
    ext; simp
  rw [this, Fin.snoc_castSucc]

theorem histProb_snoc (σ : Profile A) {T : ℕ} (h : History A T) (a : ∀ i, A i) :
    histProb σ (Fin.snoc h a : History A (T + 1)) =
      histProb σ h * ∏ j, (σ j).act T h (a j) := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun r _ => ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 := take_snoc_castSucc h a r
    simp only [Fin.val_castSucc] at h1 ⊢
    rw [Fin.snoc_castSucc]
    exact congrArg (fun x => (σ i).act r x (h r i)) h1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have h1 := take_snoc_last h a
    simp only [Fin.val_last] at h1 ⊢
    rw [Fin.snoc_last]
    exact congrArg (fun x => (σ i).act T x (a i)) h1

theorem sum_snoc {T : ℕ} {M : Type*} [AddCommMonoid M] (f : History A (T + 1) → M) :
    ∑ h : History A (T + 1), f h = ∑ h : History A T, ∑ a : (∀ i, A i), f (Fin.snoc h a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (T + 1) => ∀ i, A i)).sum_comp, Fintype.sum_prod_type_right]
  rfl

theorem sum_prob_profile (μ : ∀ j, A j → ℝ) (hμ : ∀ j, AGT.IsLottery (μ j)) :
    ∑ a : (∀ j, A j), ∏ j, μ j (a j) = 1 := by
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun j _ => (hμ j).2

theorem sum_histProb (σ : Profile A) : ∀ T : ℕ, ∑ h : History A T, histProb σ h = 1
  | 0 => by simp [histProb]
  | T + 1 => by
    rw [sum_snoc]
    simp_rw [histProb_snoc, ← Finset.mul_sum]
    rw [← sum_histProb σ T]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [sum_prob_profile _ (fun j => (σ j).act_mem T h), mul_one]

theorem stageExp_eq (g : I → (∀ i, A i) → ℝ) (σ : Profile A) (i : I) (s : ℕ) :
    stageExp g σ i s = ∑ h : History A s,
      histProb σ h * AGT.expectedPayoff g (fun j => (σ j).act s h) i := by
  unfold stageExp
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [histProb_snoc, Fin.snoc_last, AGT.expectedPayoff, AGT.profileProb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring


/-- A closed convex set contains every infinite convex combination of its points. -/
theorem mem_of_hasSum_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : Convex ℝ K) (hKc : IsClosed K) (w : ℕ → ℝ) (hw0 : ∀ s, 0 ≤ w s)
    (hw : HasSum w 1) (y : ℕ → E) (hy : ∀ s, y s ∈ K) (x : E)
    (hx : HasSum (fun s => w s • y s) x) : x ∈ K := by
  set c : ℕ → ℝ := fun N => ∑ s ∈ range N, w s
  have hc1 : ∀ N, c N ≤ 1 := fun N => sum_le_hasSum _ (fun s _ => hw0 s) hw
  have hP : ∀ N, (∑ s ∈ range N, w s • y s) + (1 - c N) • y 0 ∈ K := by
    intro N
    have := hK.sum_mem (t := range (N + 1))
      (w := fun s => if s < N then w s else 1 - c N)
      (z := fun s => if s < N then y s else y 0)
      (fun s _ => by
        split_ifs
        · exact hw0 s
        · linarith [hc1 N])
      (by
        rw [Finset.sum_range_succ]
        simp only [lt_self_iff_false, if_false]
        rw [Finset.sum_congr rfl (fun s hs => if_pos (Finset.mem_range.1 hs))]
        simp [c])
      (fun s _ => by split_ifs; exacts [hy s, hy 0])
    rw [Finset.sum_range_succ] at this
    simp only [lt_self_iff_false, if_false] at this
    rwa [Finset.sum_congr rfl (fun s hs => by
      rw [if_pos (Finset.mem_range.1 hs), if_pos (Finset.mem_range.1 hs)])] at this
  have hlim : Filter.Tendsto (fun N => (∑ s ∈ range N, w s • y s) + (1 - c N) • y 0)
      Filter.atTop (nhds (x + (1 - 1 : ℝ) • y 0)) := by
    refine hx.tendsto_sum_nat.add (Filter.Tendsto.smul_const ?_ _)
    exact tendsto_const_nhds.sub hw.tendsto_sum_nat
  simp only [sub_self, zero_smul, add_zero] at hlim
  exact hKc.mem_of_tendsto hlim (Filter.Eventually.of_forall hP)

theorem exists_bound (g : I → (∀ i, A i) → ℝ) : ∃ M, 0 < M ∧ ∀ i a, |g i a| ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range (fun p : I × (∀ i, A i) => |g p.1 p.2|)).bddAbove
  refine ⟨max M 1, by positivity, fun i a => ?_⟩
  exact (hM ⟨(i, a), rfl⟩).trans (le_max_left _ _)

theorem abs_stageExp_le (g : I → (∀ i, A i) → ℝ) (σ : Profile A) (i : I) (s : ℕ) (M : ℝ)
    (hM : ∀ i a, |g i a| ≤ M) : |stageExp g σ i s| ≤ M := by
  unfold stageExp
  calc |∑ h : History A (s + 1), histProb σ h * g i (h (Fin.last s))|
      ≤ ∑ h : History A (s + 1), |histProb σ h * g i (h (Fin.last s))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h : History A (s + 1), histProb σ h * M := by
        refine Finset.sum_le_sum fun h _ => ?_
        rw [abs_mul, abs_of_nonneg (histProb_nonneg σ h)]
        exact mul_le_mul_of_nonneg_left (hM _ _) (histProb_nonneg σ h)
    _ = M := by rw [← Finset.sum_mul, sum_histProb, one_mul]

theorem summable_payoff (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ) (hw0 : ∀ s, 0 ≤ w s)
    (hw : Summable w) (σ : Profile A) (i : I) :
    Summable (fun s => w s * stageExp g σ i s) := by
  obtain ⟨M, -, hM⟩ := exists_bound g
  refine Summable.of_norm_bounded (hw.mul_right M) fun s => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 s)]
  exact mul_le_mul_of_nonneg_left (abs_stageExp_le g σ i s M hM) (hw0 s)

theorem payoff_mem_feasible (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ) (hw0 : ∀ s, 0 ≤ w s)
    (hw : HasSum w 1) (σ : Profile A) : (fun i => payoff g w σ i) ∈ feasible g := by
  have hK : Convex ℝ (feasible g) := convex_convexHull ℝ _
  have hKc : IsClosed (feasible g) :=
    ((Set.finite_range _).isCompact_convexHull ℝ).isClosed
  refine mem_of_hasSum_convex hK hKc w hw0 hw (fun s i => stageExp g σ i s) (fun s => ?_) _ ?_
  · have : (fun i => stageExp g σ i s) =
        ∑ h : History A (s + 1), histProb σ h • (fun i => g i (h (Fin.last s))) := by
      funext i; simp [stageExp, Finset.sum_apply]
    rw [this]
    exact hK.sum_mem (fun h _ => histProb_nonneg σ h) (sum_histProb σ _)
      (fun h _ => subset_convexHull ℝ _ ⟨h (Fin.last s), rfl⟩)
  · refine Pi.hasSum.2 fun i => ?_
    exact (summable_payoff g w hw0 hw.summable σ i).hasSum


theorem abs_expectedPayoff_le (g : I → (∀ i, A i) → ℝ) (μ : ∀ j, A j → ℝ)
    (hμ : ∀ j, AGT.IsLottery (μ j)) (i : I) (M : ℝ) (hM : ∀ i a, |g i a| ≤ M) :
    |AGT.expectedPayoff g μ i| ≤ M := by
  unfold AGT.expectedPayoff AGT.profileProb
  have hp : ∀ a : (∀ j, A j), 0 ≤ ∏ j, μ j (a j) :=
    fun a => Finset.prod_nonneg fun j _ => (hμ j).1 _
  calc |∑ a : (∀ j, A j), (∏ j, μ j (a j)) * g i a|
      ≤ ∑ a : (∀ j, A j), |(∏ j, μ j (a j)) * g i a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : (∀ j, A j), (∏ j, μ j (a j)) * M := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [abs_mul, abs_of_nonneg (hp a)]
        exact mul_le_mul_of_nonneg_left (hM _ _) (hp a)
    _ = M := by rw [← Finset.sum_mul, sum_prob_profile μ hμ, one_mul]

theorem isMixed_update (μ : ∀ j, A j → ℝ) (hμ : ∀ j, AGT.IsLottery (μ j)) (i : I) (ai : A i) :
    ∀ j, AGT.IsLottery (Function.update μ i (Pi.single ai 1) j) := by
  intro j
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self]; exact isLottery_pure ai
  · simp only [Function.update_of_ne hj]; exact hμ j

/-- Against any mixed actions of the others, the best pure reply of `i` earns at least `v^i`. -/
theorem minmax_le_sup [∀ i, Nonempty (A i)] (g : I → (∀ i, A i) → ℝ) (i : I)
    (μ : ∀ j, A j → ℝ) (hμ : ∀ j, AGT.IsLottery (μ j)) :
    minmax g i ≤ ⨆ ai : A i, AGT.expectedPayoff g (Function.update μ i (Pi.single ai 1)) i := by
  obtain ⟨M, -, hM⟩ := exists_bound g
  unfold minmax
  refine ciInf_le ⟨-M, ?_⟩ (⟨μ, hμ⟩ : {μ : ∀ j, A j → ℝ // IsMixed μ})
  rintro _ ⟨ν, rfl⟩
  obtain ⟨ai⟩ := (inferInstance : Nonempty (A i))
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove ai)
  have := abs_expectedPayoff_le g _ (isMixed_update ν.1 ν.2 i ai) i M hM
  exact (abs_le.1 this).1

theorem nash_ge_minmax [∀ i, Nonempty (A i)] (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ)
    (hw0 : ∀ s, 0 ≤ w s) (hw : HasSum w 1) (ρ : Profile A) (hN : IsNash g w ρ) (i : I) :
    minmax g i ≤ payoff g w ρ i := by
  -- the myopic best reply of `i`
  have hbr : ∀ (t : ℕ) (h : History A t), ∃ b : A i, ∀ ai : A i,
      AGT.expectedPayoff g (Function.update (fun j => (ρ j).act t h) i (Pi.single ai 1)) i ≤
        AGT.expectedPayoff g (Function.update (fun j => (ρ j).act t h) i (Pi.single b 1)) i :=
    fun t h => Finite.exists_max _
  choose br hbr using hbr
  let τ : Strategy A i := ⟨fun t h => Pi.single (br t h) 1, fun t h => isLottery_pure _⟩
  have hact : ∀ t (h : History A t),
      (fun j => (Function.update ρ i τ j).act t h) =
        Function.update (fun j => (ρ j).act t h) i (Pi.single (br t h) 1) := by
    intro t h
    funext j
    by_cases hj : j = i
    · subst hj; simp [τ]
    · simp [Function.update_of_ne hj]
  have hstage : ∀ s, minmax g i ≤ stageExp g (Function.update ρ i τ) i s := by
    intro s
    rw [stageExp_eq]
    calc minmax g i = ∑ h : History A s, histProb (Function.update ρ i τ) h * minmax g i := by
          rw [← Finset.sum_mul, sum_histProb, one_mul]
      _ ≤ _ := by
          refine Finset.sum_le_sum fun h _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (histProb_nonneg _ h)
          rw [hact s h]
          refine (minmax_le_sup g i _ (fun j => (ρ j).act_mem s h)).trans ?_
          exact ciSup_le (hbr s h)
  have hle : minmax g i ≤ payoff g w (Function.update ρ i τ) i := by
    unfold payoff
    calc minmax g i = ∑' s, w s * minmax g i := by rw [tsum_mul_right, hw.tsum_eq, one_mul]
      _ ≤ _ := by
          refine Summable.tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left (hstage s) (hw0 s))
            (hw.summable.mul_right _) (summable_payoff g w hw0 hw.summable _ i)
  exact hle.trans (hN i τ)


theorem restrict_nil (σ : Profile A) (h0 : History A 0) : restrict σ h0 = σ := by
  funext i
  have hh0 : h0 = Fin.elim0 := Subsingleton.elim _ _
  subst hh0
  rcases hσ : σ i with ⟨act, hact⟩
  simp only [TimeDepFolk.Asymptotic.restrict, hσ, Fin.elim0_append]
  congr 1
  funext t h'
  have key : ∀ m (e : m = t), act m (h' ∘ Fin.cast e) = act t h' := by
    intro m e; subst e; rfl
  exact key _ (Nat.zero_add t)

theorem cont_zero (θ : Evaluation) : cont θ.θ 0 = θ.θ := by
  funext s
  simp [cont, θ.hasSum.tsum_eq]

theorem eqPayoffs_subset_F [∀ i, Nonempty (A i)] (g : I → (∀ i, A i) → ℝ) (θ : Evaluation) :
    eqPayoffs g θ ⊆ F g := by
  rintro x ⟨σ, hσ, hx⟩
  have hxe : x = fun i => payoff g θ.θ σ i := funext fun i => (hx i).symm
  subst hxe
  have hN : IsNash g θ.θ σ := by
    have := hσ 0 Fin.elim0
    rwa [restrict_nil, cont_zero] at this
  exact ⟨payoff_mem_feasible g θ.θ θ.nonneg θ.hasSum σ,
    fun i => nash_ge_minmax g θ.θ θ.nonneg θ.hasSum σ hN i⟩

end TDFAux

open TimeDepFolk.Asymptotic

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (g : I → (∀ i, A i) → ℝ) (hint : (interior (F g)).Nonempty)
    (θ : ℕ → Evaluation) (hθ : IsPatient θ) :
    Filter.Tendsto (fun k => Metric.hausdorffEDist (eqPayoffs g (θ k)) (F g))
      Filter.atTop (nhds 0) := by
  -- `F` is compact and convex, and is the closure of its interior
  have hFc : IsCompact (F g) := by
    have h1 : IsCompact (feasible g) := (Set.finite_range _).isCompact_convexHull ℝ
    have h2 : IsClosed {x : I → ℝ | ∀ i, minmax g i ≤ x i} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    exact h1.inter_right h2
  have hFconv : Convex ℝ (F g) := by
    have h2 : Convex ℝ {x : I → ℝ | ∀ i, minmax g i ≤ x i} := by
      intro x hx y hy a b ha hb hab i
      have := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e : a * minmax g i + b * minmax g i = minmax g i := by rw [← add_mul, hab, one_mul]
      linarith
    exact (convex_convexHull ℝ _).inter h2
  have hcl : F g ⊆ closure (interior (F g)) := by
    rw [hFconv.closure_interior_eq_closure_of_nonempty_interior hint]
    exact subset_closure
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  -- a finite `ε`-net of `F` made of interior points
  obtain ⟨t, ht⟩ := hFc.elim_finite_subcover
    (fun p : interior (F g) => Metric.eball (p : I → ℝ) ε)
    (fun p => Metric.isOpen_eball) (by
      intro f hf
      obtain ⟨p, hp, hfp⟩ := EMetric.mem_closure_iff.1 (hcl hf) ε hε
      exact Set.mem_iUnion.2 ⟨⟨p, hp⟩, Metric.mem_eball.2 hfp⟩)
  have hev : ∀ p ∈ t, ∀ᶠ k in Filter.atTop, (p : I → ℝ) ∈ eqPayoffs g (θ k) := by
    intro p _
    obtain ⟨K, hK⟩ := interior_mem_eqPayoffs g hint θ hθ p p.2
    exact Filter.eventually_atTop.2 ⟨K, hK⟩
  filter_upwards [(Filter.eventually_all_finset t).2 hev] with k hk
  refine Metric.hausdorffEDist_le_of_mem_edist ?_ ?_
  · intro x hx
    exact ⟨x, TDFAux.eqPayoffs_subset_F g (θ k) hx, by simp⟩
  · intro f hf
    obtain ⟨p, hpt, hfp⟩ := Set.mem_iUnion₂.1 (ht hf)
    exact ⟨p, hk p hpt, (Metric.mem_eball.1 hfp).le⟩
