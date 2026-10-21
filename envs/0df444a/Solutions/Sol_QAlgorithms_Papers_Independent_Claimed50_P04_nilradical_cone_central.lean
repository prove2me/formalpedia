-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P04.nilradical_cone_central
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:03:57.48861+00:00
-- url     : https://prove2.me/submissions/f2f1c824-c76b-4771-9ee4-7270a95fe705

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P04
open QAlgorithms.Papers.Independent.Claimed50.P04

noncomputable section

open Set

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Frontier30.P26
  (Invariant LieAdmissible ClosedCone CompactlyEmbedded CompactCartan Hermitian bracketSpan
    TubeType)

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedSpace

section G59BExp

open QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates (expAd adMap)

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]

open scoped Nat

theorem g59b_exp_summable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (y : E) :
    Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (T ^ n) y) := by
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  let T' : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    LinearMap.toContinuousLinearMap
      (e.toLinearEquiv.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearEquiv.toLinearMap)
  have hs : Summable (fun n : ℕ => ((n ! : ℝ)⁻¹) • T' ^ n) :=
    NormedSpace.expSeries_summable' T'
  have hpow : ∀ n : ℕ, (T' ^ n) (e y) = e ((T ^ n) y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, pow_succ', Module.End.mul_apply]
      simp [T']
  have h2 := (hs.mapL (ContinuousLinearMap.apply ℝ _ (e y))).mapL
    (e.symm : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E)
  convert h2 using 1
  ext n
  simp [hpow]

theorem g59b_exp_transport {E V : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (e : E ≃L[ℝ] V) (T : E →ₗ[ℝ] E) (T' : V →L[ℝ] V) (hT : ∀ v, T' v = e (T (e.symm v)))
    (y : E) :
    e (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (T ^ n) y) = NormedSpace.exp T' (e y) := by
  have hpow : ∀ n : ℕ, (T' ^ n) (e y) = e ((T ^ n) y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, pow_succ', Module.End.mul_apply, hT]
      simp
  have h1 := (g59b_exp_summable T y).hasSum.map (e : E →L[ℝ] V) e.continuous
  have h2 := ((NormedSpace.expSeries_summable' (𝕂 := ℝ) T').hasSum).mapL
    (ContinuousLinearMap.apply ℝ V (e y))
  rw [NormedSpace.exp_eq_tsum ℝ]
  refine h1.unique ?_
  convert h2 using 1
  · ext n
    simp [hpow]
  · rfl

theorem g59b_lie_mem_of_exp
    (M : Submodule ℝ A) (x y : A) (h : ∀ t : ℝ, expAd (t • x) y ∈ M) : ⁅x, y⁆ ∈ M := by
  let e : A ≃L[ℝ] (Fin (Module.finrank ℝ A) → ℝ) :=
    (Module.finBasis ℝ A).equivFun.toContinuousLinearEquiv
  let T' : (Fin (Module.finrank ℝ A) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ A) → ℝ) :=
    LinearMap.toContinuousLinearMap
      (e.toLinearEquiv.toLinearMap ∘ₗ adMap x ∘ₗ e.symm.toLinearEquiv.toLinearMap)
  have hg : ∀ t : ℝ, e (expAd (t • x) y) = (NormedSpace.exp (t • T')) (e y) := by
    intro t
    unfold expAd
    apply g59b_exp_transport e (adMap (t • x)) (t • T')
    intro v
    simp [T', adMap]
  have hd : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • T')) (e y)) (T' (e y)) 0 := by
    have h1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) T' 0).clm_apply (hasDerivAt_const (0:ℝ) (e y))
    simpa using h1
  have ht := hasDerivAt_iff_tendsto_slope_zero.1 hd
  have ht2 := ((e.symm : (Fin (Module.finrank ℝ A) → ℝ) →L[ℝ] A).continuous.tendsto _).comp ht
  have hlim : (e.symm : (Fin (Module.finrank ℝ A) → ℝ) →L[ℝ] A) (T' (e y)) = ⁅x, y⁆ := by
    simp [T', adMap]
  rw [hlim] at ht2
  refine (Submodule.closed_of_finiteDimensional M).mem_of_tendsto ht2 (Filter.Eventually.of_forall ?_)
  intro t
  simp only [Function.comp_apply, zero_add, map_smul, map_sub]
  rw [← hg, ← hg]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  exact M.smul_mem _ (M.sub_mem (h t) (h 0))

theorem g59b_exp_add (x u v : A) : expAd x (u + v) = expAd x u + expAd x v := by
  unfold expAd
  rw [← (g59b_exp_summable (adMap x) u).tsum_add (g59b_exp_summable (adMap x) v)]
  congr 1; ext n; simp [smul_add]

theorem g59b_exp_smul (x u : A) (r : ℝ) : expAd x (r • u) = r • expAd x u := by
  unfold expAd
  rw [← (g59b_exp_summable (adMap x) u).tsum_const_smul r]
  congr 1; ext n; simp [smul_comm r]

theorem g59b_exp_zero (x : A) : expAd x (0 : A) = 0 := by
  simpa using g59b_exp_smul x (0 : A) 0

theorem g59b_exp_mem (M : Submodule ℝ A) (x : A) (hM : ∀ m ∈ M, ⁅x, m⁆ ∈ M) (m : A) (hm : m ∈ M) :
    expAd x m ∈ M := by
  have hpow : ∀ n : ℕ, ((adMap x) ^ n) m ∈ M := by
    intro n
    induction n with
    | zero => simpa using hm
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hM _ ih
  unfold expAd
  exact (Submodule.closed_of_finiteDimensional M).mem_of_tendsto
    (g59b_exp_summable (adMap x) m).hasSum
    (Filter.Eventually.of_forall (fun s => M.sum_mem (fun n _ => M.smul_mem _ (hpow n))))

theorem g59b_exp3 (y c : A) (h : ⁅y, ⁅y, ⁅y, c⁆⁆⁆ = 0) (s : ℝ) :
    expAd (s • y) c = c + s • ⁅y, c⁆ + (s ^ 2 / 2) • ⁅y, ⁅y, c⁆⁆ := by
  unfold expAd
  have h3 : ∀ m : ℕ, (adMap (s • y) ^ (m + 3)) c = 0 := by
    intro m
    rw [pow_add, Module.End.mul_apply]
    have : (adMap (s • y) ^ 3) c = 0 := by
      simp [pow_succ, adMap, h]
    rw [this, map_zero]
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp [Finset.sum_range_succ, adMap, pow_succ, smul_smul, Nat.factorial]
    module
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    rw [h3, smul_zero]

end G59BExp

section G59BMain

def g59b_T {G : Type*} [LieRing G] [LieAlgebra ℝ G] (a E : Submodule ℝ G) : ℕ → G → Prop
  | 0, y => y ∈ E
  | (k+1), y => ∀ c ∈ a, g59b_T a E k ⁅y, c⁆

theorem g59b_T_chain {G : Type*} [LieRing G] [LieAlgebra ℝ G] (a E : Submodule ℝ G)
    (hbr : ∀ y ∈ a, ∀ c ∈ a, ⁅y, c⁆ ∈ a)
    (hkey : ∀ y ∈ a, g59b_T a E 2 y → g59b_T a E 1 y) :
    ∀ k, ∀ y ∈ a, g59b_T a E (k + 1) y → g59b_T a E 1 y := by
  have D : ∀ k, ∀ y ∈ a, g59b_T a E (k + 2) y → g59b_T a E (k + 1) y := by
    intro k
    induction k with
    | zero => exact hkey
    | succ k ih =>
      intro y hy h c hc
      exact ih _ (hbr y hy c hc) (h c hc)
  intro k
  induction k with
  | zero => intro y _ h; exact h
  | succ k ih => intro y hy h; exact ih y hy (D k y hy h)

theorem g59b_T_nil {G : Type*} [LieRing G] [LieAlgebra ℝ G] (a E : Submodule ℝ G)
    (U : LieIdeal ℝ G) (haU : ∀ c ∈ a, c ∈ U) (m : ℕ)
    (hm : LieModule.lowerCentralSeries ℝ U U m = ⊥) :
    ∀ j k (y : U), y ∈ LieModule.lowerCentralSeries ℝ U U k → m ≤ k + j →
      g59b_T a E j (y : G) := by
  intro j
  induction j with
  | zero =>
    intro k y hy hk
    have : y ∈ LieModule.lowerCentralSeries ℝ U U m :=
      LieModule.antitone_lowerCentralSeries ℝ U U (by omega) hy
    rw [hm] at this
    have : y = 0 := (LieSubmodule.mem_bot y).1 this
    subst this
    exact E.zero_mem
  | succ j ih =>
    intro k y hy hk c hc
    have hcU := haU c hc
    have hmem : ⁅y, (⟨c, hcU⟩ : U)⁆ ∈ LieModule.lowerCentralSeries ℝ U U (k + 1) := by
      rw [LieModule.lowerCentralSeries_succ, ← lie_skew]
      exact neg_mem (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hy)
    have := ih (k + 1) _ hmem (by omega)
    simpa using this

end G59BMain

section LieDefinitions

open QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates (expAd adMap)

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

theorem solution (ha : LieAdmissible (G := G))
    (U : LieIdeal ℝ G) (hu : MaximalNilpotent U) (W : Set G)
    (hw : GeneratingCone W) (hline : Lineality W ⊆ LieAlgebra.center ℝ G) :
    W ∩ (U : Set G) ⊆ LieAlgebra.center ℝ G := by
  rintro x ⟨hxW, hxU⟩
  obtain ⟨⟨hcl, hcv, h0, hsm⟩, hinv, hspan⟩ := hw
  have hadd : ∀ u ∈ W, ∀ v ∈ W, u + v ∈ W := by
    intro u hu v hv
    have := hcv hu hv (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have h2 := hsm 2 (by norm_num) _ this
    convert h2 using 1
    simp only [smul_add, smul_smul]; norm_num
  let E : Submodule ℝ G :=
    { carrier := {e | e ∈ W ∧ -e ∈ W}
      add_mem' := by
        rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
        exact ⟨hadd _ hu1 _ hv1, by simpa [neg_add, add_comm] using hadd _ hu2 _ hv2⟩
      zero_mem' := ⟨h0, by simpa using h0⟩
      smul_mem' := by
        rintro r u ⟨hu1, hu2⟩
        rcases le_total 0 r with hr | hr
        · exact ⟨hsm r hr _ hu1, by simpa using hsm r hr _ hu2⟩
        · refine ⟨?_, ?_⟩
          · simpa using hsm (-r) (by linarith) _ hu2
          · simpa using hsm (-r) (by linarith) _ hu1 }
  have hmemE : ∀ e, e ∈ E ↔ e ∈ W ∧ -e ∈ W := fun e => Iff.rfl
  have hElin : ∀ e ∈ E, e ∈ Lineality W := by
    intro e ⟨he1, he2⟩
    ext c
    constructor
    · rintro ⟨d, hd, rfl⟩; exact hadd _ hd _ he1
    · intro hc
      exact ⟨c + -e, hadd _ hc _ he2, by abel⟩
  have hEc : ∀ e ∈ E, ∀ z : G, ⁅z, e⁆ = 0 := by
    intro e he z
    have := hline (hElin e he)
    exact (LieModule.mem_maxTrivSubmodule ℝ G G e).1 this z
  have hWE : ∀ w ∈ W, ∀ e ∈ E, w + e ∈ W := fun w hw e he => hadd _ hw _ he.1
  have hlim : ∀ w ∈ W, ∀ u : G, (∀ s : ℝ, w + s • u ∈ W) → u ∈ W := by
    intro w hw u h
    have ht : Filter.Tendsto (fun l : ℝ => l⁻¹ • w + u) Filter.atTop (nhds u) := by
      have := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const w).add_const u
      simpa using this
    refine hcl.mem_of_tendsto ht ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with l hl
    have := hsm l⁻¹ (inv_nonneg.2 hl.le) _ (h l)
    rwa [smul_add, smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at this
  have hL2 : ∀ w ∈ W, ∀ u : G, (∀ s : ℝ, w + s • u ∈ W) → u ∈ E := by
    intro w hw u h
    refine ⟨hlim w hw u h, hlim w hw (-u) (fun s => by simpa using h (-s))⟩
  have hWinv : ∀ y : G, ∀ w ∈ W, expAd y w ∈ W := by
    intro y w hw
    have := hinv y
    rw [← this]
    exact ⟨w, hw, rfl⟩
  have hK : ∀ y c : G, c ∈ W → ⁅y, ⁅y, c⁆⁆ ∈ E → ⁅y, c⁆ ∈ E := by
    intro y c hc he
    apply hL2 c hc
    intro s
    have h3 : ⁅y, ⁅y, ⁅y, c⁆⁆⁆ = 0 := hEc _ he y
    have := hWE _ (hWinv (s • y) c hc) (-(s ^ 2 / 2) • ⁅y, ⁅y, c⁆⁆) (E.smul_mem _ he)
    rw [g59b_exp3 y c h3 s] at this
    convert this using 1
    module
  -- the span of W ∩ U
  let a : Submodule ℝ G := Submodule.span ℝ (W ∩ (U : Set G))
  have haU : ∀ c ∈ a, c ∈ U := by
    intro c hc
    have : a ≤ U.toSubmodule := Submodule.span_le.2 (fun z hz => hz.2)
    exact this hc
  have hUinv : ∀ y : G, ∀ u ∈ U, expAd y u ∈ U := by
    intro y u hu
    exact g59b_exp_mem U.toSubmodule y (fun m hm => U.lie_mem hm) u hu
  have haexp : ∀ y : G, ∀ c ∈ a, expAd y c ∈ a := by
    intro y c hc
    induction hc using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨hWinv y z hz.1, hUinv y z hz.2⟩
    | zero => rw [g59b_exp_zero]; exact a.zero_mem
    | add u v _ _ hu hv => rw [g59b_exp_add]; exact a.add_mem hu hv
    | smul r u _ hu => rw [g59b_exp_smul]; exact a.smul_mem r hu
  have haideal : ∀ y : G, ∀ c ∈ a, ⁅y, c⁆ ∈ a := by
    intro y c hc
    exact g59b_lie_mem_of_exp a y c (fun t => haexp _ c hc)
  -- key step
  have hkey : ∀ y ∈ a, g59b_T a E 2 y → g59b_T a E 1 y := by
    intro y hy h2 c hc
    show ⁅y, c⁆ ∈ E
    induction hc using Submodule.span_induction with
    | mem z hz =>
      apply hK y z hz.1
      have := h2 z (Submodule.subset_span hz) y hy
      change ⁅⁅y, z⁆, y⁆ ∈ E at this
      rw [← lie_skew]
      exact E.neg_mem this
    | zero => simp
    | add u v _ _ hu hv => rw [lie_add]; exact E.add_mem hu hv
    | smul r u _ hu => rw [lie_smul]; exact E.smul_mem r hu
  obtain ⟨m, hm⟩ := (LieModule.isNilpotent_iff ℝ U U).1 hu.1
  have hT1 : ∀ y ∈ a, g59b_T a E 1 y := by
    intro y hy
    apply g59b_T_chain a E (fun y _ c hc => haideal y c hc) hkey m y hy
    have := g59b_T_nil a E U haU m hm (m + 1) 0 ⟨y, haU y hy⟩ (by simp) (by omega)
    exact this
  have hxa : x ∈ a := Submodule.subset_span ⟨hxW, hxU⟩
  -- [x, w] ∈ E for w ∈ W
  have hxw : ∀ w ∈ W, ⁅x, w⁆ ∈ E := by
    intro w hw
    apply hK x w hw
    have : ⁅x, w⁆ ∈ a := by
      rw [← lie_skew]; exact a.neg_mem (haideal w x hxa)
    exact hT1 x hxa _ this
  have hxz : ∀ z : G, ⁅x, z⁆ ∈ E := by
    intro z
    have hz : z ∈ Submodule.span ℝ W := by rw [hspan]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz => exact hxw z hz
    | zero => simp
    | add u v _ _ hu hv => rw [lie_add]; exact E.add_mem hu hv
    | smul r u _ hu => rw [lie_smul]; exact E.smul_mem r hu
  have hx2 : ∀ z : G, ⁅x, ⁅x, z⁆⁆ = 0 := fun z => hEc _ (hxz z) x
  -- admissibility
  obtain ⟨C, hCcl, hCcv, hCpt, hCinv, hCspan⟩ := ha
  have hCinv' : ∀ y : G, ∀ c ∈ C, expAd y c ∈ C := by
    intro y c hc
    have := hCinv y
    rw [← this]
    exact ⟨c, hc, rfl⟩
  have hrec : ∀ c ∈ C, ∀ d : G, (∀ s : ℝ, 0 ≤ s → c + s • d ∈ C) →
      d ∈ QAlgorithms.Papers.Independent.Frontier30.P26.recession C := by
    intro c hc d h c' hc'
    have ht : Filter.Tendsto (fun t : ℝ => (1 - t) • c' + t • c + d)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (c' + d)) := by
      have h1 : Filter.Tendsto (fun t : ℝ => (1 - t) • c' + t • c + d) (nhds 0)
          (nhds (((1:ℝ) - 0) • c' + (0:ℝ) • c + d)) := by
        apply Filter.Tendsto.add_const
        apply Filter.Tendsto.add
        · exact (((tendsto_const_nhds (x := (1:ℝ))).sub Filter.tendsto_id).smul_const c')
        · exact Filter.tendsto_id.smul_const c
      simpa using h1.mono_left nhdsWithin_le_nhds
    refine hCcl.mem_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have := hCcv hc' (h t⁻¹ (inv_nonneg.2 ht0.le)) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
      (by ring)
    convert this using 1
    rw [smul_add (t : ℝ) c, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul, add_assoc]
  have hxc : ∀ c ∈ C, ⁅x, c⁆ = 0 := by
    intro c hc
    have hline' : ∀ s : ℝ, c + s • ⁅x, c⁆ ∈ C := by
      intro s
      have := hCinv' (s • x) c hc
      rw [g59b_exp3 x c (by simp [hx2]) s, hx2, smul_zero, add_zero] at this
      exact this
    apply hCpt
    · exact hrec c hc _ (fun s _ => hline' s)
    · exact hrec c hc _ (fun s _ => by have := hline' (-s); rwa [neg_smul, ← smul_neg] at this)
  have hxall : ∀ z : G, ⁅x, z⁆ = 0 := by
    intro z
    have hz : z ∈ Submodule.span ℝ C := by rw [hCspan]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz => exact hxc z hz
    | zero => simp
    | add u v _ _ hu hv => rw [lie_add, hu, hv, add_zero]
    | smul r u _ hu => rw [lie_smul, hu, smul_zero]
  show x ∈ LieModule.maxTrivSubmodule ℝ G G
  rw [LieModule.mem_maxTrivSubmodule]
  intro z
  rw [← lie_skew, hxall z, neg_zero]

end LieDefinitions
