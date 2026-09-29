-- Prove2me | solution 1 for WhitneyEmbedding.injective_immersion_of_blockwise_immersions
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T16:45:25.1948+00:00
-- url     : https://prove2.me/submissions/8882ab7e-4e6d-4820-b4f3-308480264803

import Mathlib

open Function Filter Module Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace BlockGlue

/-- A smooth bump on `ℝ` which is positive exactly on `(-1,1)`. -/
noncomputable def chi (t : ℝ) : ℝ := Real.smoothTransition (1 - t ^ 2)

lemma chi_contDiff : ContDiff ℝ ∞ chi :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

lemma chi_pos {t : ℝ} (h : |t| < 1) : 0 < chi t := by
  refine Real.smoothTransition.pos_of_pos ?_
  nlinarith [sq_abs t, abs_nonneg t]

lemma chi_eq_zero {t : ℝ} (h : 1 ≤ |t|) : chi t = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  nlinarith [sq_abs t, abs_nonneg t]

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The weight attached to the block centred at the integer `j`. -/
def wt (r : M → ℝ) (j : ℤ) (x : M) : ℝ := chi (r x - j)

omit [TopologicalSpace M] in
lemma wt_eq_zero {r : M → ℝ} {j : ℤ} {x : M} (h : 1 ≤ |r x - j|) : wt r j x = 0 :=
  chi_eq_zero h

omit [TopologicalSpace M] in
lemma wt_pos {r : M → ℝ} {j : ℤ} {x : M} (h : |r x - j| < 1) : 0 < wt r j x :=
  chi_pos h

/-- The sum of the blocks of a fixed parity `p`. -/
def blockSum (r : M → ℝ) (g : ℤ → M → EuclideanSpace ℝ (Fin m)) (p : ℤ) (x : M) :
    EuclideanSpace ℝ (Fin m) :=
  ∑ᶠ k : ℤ, wt r (2 * k + p) x • g (2 * k + p) x

omit [TopologicalSpace M] in
/-- Away from its own block, a weight vanishes. -/
lemma wt_eq_zero_of_ne {r : M → ℝ} {p k k' : ℤ} {x : M} (hx : |r x - (2 * k + p)| < 1)
    (hk : k' ≠ k) : wt r (2 * k' + p) x = 0 := by
  refine wt_eq_zero ?_
  rw [abs_lt] at hx
  push_cast at hx ⊢
  rw [le_abs]
  rcases (by omega : k' ≤ k - 1 ∨ k + 1 ≤ k') with h | h
  · have h' : (k' : ℝ) ≤ (k : ℝ) - 1 := by exact_mod_cast h
    left; linarith
  · have h' : (k : ℝ) + 1 ≤ (k' : ℝ) := by exact_mod_cast h
    right; linarith

lemma locallyFinite_blocks {r : M → ℝ} (hr : Continuous r)
    (g : ℤ → M → EuclideanSpace ℝ (Fin m)) (p : ℤ) :
    LocallyFinite fun k : ℤ => support fun x => wt r (2 * k + p) x • g (2 * k + p) x := by
  intro x
  refine ⟨r ⁻¹' Set.Ioo (r x - 1) (r x + 1),
    hr.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
  refine Set.Finite.subset (Set.finite_Icc (⌈(r x - 3 - p) / 2⌉) (⌊(r x + 3 - p) / 2⌋)) ?_
  rintro k ⟨y, hy, hyU⟩
  have hw : wt r (2 * k + p) y ≠ 0 := fun h => hy (by simp [Function.mem_support, h] at hy ⊢)
  have hy1 : |r y - ((2 * k + p : ℤ) : ℝ)| < 1 := by
    by_contra h
    exact hw (wt_eq_zero (not_lt.1 h))
  rw [abs_lt] at hy1
  push_cast at hy1
  have hyU' : r y ∈ Set.Ioo (r x - 1) (r x + 1) := hyU
  obtain ⟨hy2, hy3⟩ := hyU'
  constructor
  · exact Int.ceil_le.2 (by rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]; linarith)
  · exact Int.le_floor.2 (by rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]; linarith)

omit [TopologicalSpace M] in
lemma blockSum_eq_single {r : M → ℝ} {g : ℤ → M → EuclideanSpace ℝ (Fin m)} {p k : ℤ} {x : M}
    (hx : |r x - (2 * k + p)| < 1) :
    blockSum r g p x = wt r (2 * k + p) x • g (2 * k + p) x := by
  refine finsum_eq_single _ k ?_
  intro k' hk'
  rw [wt_eq_zero_of_ne hx hk', zero_smul]

lemma blockSum_eventuallyEq {r : M → ℝ} (hr : Continuous r)
    {g : ℤ → M → EuclideanSpace ℝ (Fin m)} {p k : ℤ} {x : M}
    (hx : |r x - (2 * k + p)| < 1) :
    blockSum r g p =ᶠ[𝓝 x] fun y => wt r (2 * k + p) y • g (2 * k + p) y := by
  have hU : IsOpen {y : M | |r y - (2 * (k : ℝ) + (p : ℝ))| < 1} :=
    isOpen_lt ((continuous_abs.comp (hr.sub continuous_const))) continuous_const
  exact eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => blockSum_eq_single hy

omit [IsManifold (𝓡 n) ∞ M] in
lemma contMDiff_wt {r : M → ℝ} (hr : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r) (j : ℤ) :
    ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (wt r j) :=
  (chi_contDiff.contMDiff).comp (hr.sub contMDiff_const)

omit [IsManifold (𝓡 n) ∞ M] in
lemma contMDiff_blockSum {r : M → ℝ} (hr : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r)
    {g : ℤ → M → EuclideanSpace ℝ (Fin m)} (hg : ∀ j, ContMDiff (𝓡 n) (𝓡 m) ∞ (g j)) (p : ℤ) :
    ContMDiff (𝓡 n) (𝓡 m) ∞ (blockSum r g p) :=
  contMDiff_finsum (fun _ => (contMDiff_wt hr _).smul (hg _))
    (locallyFinite_blocks hr.continuous g p)

omit [IsManifold (𝓡 n) ∞ M] in
/-- Leibniz rule for a scalar function times a vector-valued function on a manifold. -/
lemma hasMFDerivAt_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {u : M → ℝ}
    {G : M → V} {x : M} {u' : TangentSpace (𝓡 n) x →L[ℝ] ℝ}
    {G' : TangentSpace (𝓡 n) x →L[ℝ] V}
    (hu : HasMFDerivAt (𝓡 n) 𝓘(ℝ) u x u') (hG : HasMFDerivAt (𝓡 n) 𝓘(ℝ, V) G x G') :
    HasMFDerivAt (𝓡 n) 𝓘(ℝ, V) (fun y => u y • G y) x (u x • G' + u'.smulRight (G x)) := by
  refine ⟨hu.1.smul hG.1, ?_⟩
  have h := hu.2.smul hG.2
  simp only [mfld_simps, Function.comp_def] at h ⊢
  exact h

/-- If `D v = 0` then `(L ∘ D) v = 0`. -/
lemma clm_comp_apply_zero {X Y W : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace W] [AddCommGroup W]
    [Module ℝ W] (L : Y →L[ℝ] W) (D : X →L[ℝ] Y) {v : X} (hv : D v = 0) : (L.comp D) v = 0 := by
  rw [ContinuousLinearMap.comp_apply, hv, map_zero]

/-- Evaluation of `a • D + L.smulRight z` at a vector killed by `L`. -/
lemma clm_add_smulRight_apply {X W : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (a : ℝ) (D : X →L[ℝ] W) (L : X →L[ℝ] ℝ) (z : W)
    (v : X) (hL : L v = 0) : (a • D + L.smulRight z) v = a • D v := by
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, hL, zero_smul, add_zero,
    ContinuousLinearMap.smul_apply]

omit [IsManifold (𝓡 n) ∞ M] in
/-- On the block around `2 * k + p`, the derivative of the parity-`p` sum in a direction killed by
`dr` is a positive multiple of the derivative of `g (2 * k + p)`. -/
lemma mfderiv_blockSum_apply {r : M → ℝ} (hr : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r)
    {g : ℤ → M → EuclideanSpace ℝ (Fin m)} (hg : ∀ j, ContMDiff (𝓡 n) (𝓡 m) ∞ (g j)) {p k : ℤ}
    {x : M} (hx : |r x - (2 * k + p)| < 1) (v : TangentSpace (𝓡 n) x)
    (hv : mfderiv (𝓡 n) 𝓘(ℝ) r x v = 0) :
    mfderiv (𝓡 n) (𝓡 m) (blockSum r g p) x v =
      wt r (2 * k + p) x • mfderiv (𝓡 n) (𝓡 m) (g (2 * k + p)) x v := by
  obtain ⟨Dr, hDr⟩ : ∃ D : TangentSpace (𝓡 n) x →L[ℝ] ℝ, HasMFDerivAt (𝓡 n) 𝓘(ℝ) r x D :=
    ⟨_, ((hr x).mdifferentiableAt (by simp)).hasMFDerivAt⟩
  obtain ⟨Dg, hDg⟩ : ∃ D : TangentSpace (𝓡 n) x →L[ℝ] EuclideanSpace ℝ (Fin m),
      HasMFDerivAt (𝓡 n) (𝓡 m) (g (2 * k + p)) x D :=
    ⟨_, ((hg (2 * k + p) x).mdifferentiableAt (by simp)).hasMFDerivAt⟩
  have hDrv : Dr v = 0 := by rw [← hDr.mfderiv]; exact hv
  have hφ : HasFDerivAt (fun t : ℝ => chi (t - ((2 * k + p : ℤ) : ℝ)))
      (fderiv ℝ (fun t : ℝ => chi (t - ((2 * k + p : ℤ) : ℝ))) (r x)) (r x) :=
    (((chi_contDiff.comp (contDiff_id.sub contDiff_const)).differentiable (by simp))
      (r x)).hasFDerivAt
  have hu : HasMFDerivAt (𝓡 n) 𝓘(ℝ) (wt r (2 * k + p)) x
      ((fderiv ℝ (fun t : ℝ => chi (t - ((2 * k + p : ℤ) : ℝ))) (r x)).comp Dr) :=
    hφ.hasMFDerivAt.comp x hDr
  have hB := (hasMFDerivAt_smul hu hDg).congr_of_eventuallyEq
    (blockSum_eventuallyEq (g := g) hr.continuous hx)
  rw [hB.mfderiv, hDg.mfderiv]
  refine clm_add_smulRight_apply (X := TangentSpace (𝓡 n) x) (W := EuclideanSpace ℝ (Fin m))
    _ _ _ _ v ?_
  rw [ContinuousLinearMap.comp_apply, hDrv, map_zero]

/-- Every real number lies within `1/2` of a point of the form `2 * k + i` with `i : Fin 2`. -/
lemma exists_block (t : ℝ) :
    ∃ (i : Fin 2) (k : ℤ), |t - (2 * (k : ℝ) + (((i : ℕ) : ℤ) : ℝ))| ≤ 1 / 2 := by
  have h := abs_sub_round t
  rcases Int.even_or_odd (round t) with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨0, k, ?_⟩
    have hc : (2 * (k : ℝ) + ((((0 : Fin 2) : ℕ) : ℤ) : ℝ)) = ((round t : ℤ) : ℝ) := by
      rw [hk]; push_cast [Fin.val_zero, Fin.val_one]; ring
    rw [hc]; exact h
  · refine ⟨1, k, ?_⟩
    have hc : (2 * (k : ℝ) + ((((1 : Fin 2) : ℕ) : ℤ) : ℝ)) = ((round t : ℤ) : ℝ) := by
      rw [hk]; push_cast [Fin.val_zero, Fin.val_one]; ring
    rw [hc]; exact h

/-- The glued map: the two parity sums together with `r`. -/
def glueMap (r : M → ℝ) (g : ℤ → M → EuclideanSpace ℝ (Fin m)) :
    M → ((Fin 2 → EuclideanSpace ℝ (Fin m)) × ℝ) :=
  fun x => (fun i : Fin 2 => blockSum r g ((i : ℕ) : ℤ) x, r x)

omit [IsManifold (𝓡 n) ∞ M] in
lemma contMDiff_glueMap {r : M → ℝ} (hr : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r)
    {g : ℤ → M → EuclideanSpace ℝ (Fin m)} (hg : ∀ j, ContMDiff (𝓡 n) (𝓡 m) ∞ (g j)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, (Fin 2 → EuclideanSpace ℝ (Fin m)) × ℝ) ∞ (glueMap r g) :=
  (contMDiff_pi_space.2 fun i : Fin 2 => contMDiff_blockSum hr hg ((i : ℕ) : ℤ)).prodMk_space hr

omit [TopologicalSpace M] [IsManifold (𝓡 n) ∞ M] in
lemma glueMap_injective {r : M → ℝ} {g : ℤ → M → EuclideanSpace ℝ (Fin m)}
    (hginj : ∀ j : ℤ, InjOn (g j) (r ⁻¹' (Set.Icc ((j : ℝ) - 1) ((j : ℝ) + 1)))) :
    Injective (glueMap r g) := by
  intro x y hxy
  simp only [glueMap, Prod.mk.injEq] at hxy
  obtain ⟨h1, hr_eq⟩ := hxy
  obtain ⟨i, k, hik⟩ := exists_block (r x)
  set p : ℤ := ((i : ℕ) : ℤ) with hp
  have hx1 : |r x - (2 * (k : ℝ) + (p : ℝ))| < 1 := lt_of_le_of_lt hik (by norm_num)
  have hik' : |r y - (2 * (k : ℝ) + (p : ℝ))| ≤ 1 / 2 := by rw [← hr_eq]; exact hik
  have hy1 : |r y - (2 * (k : ℝ) + (p : ℝ))| < 1 := lt_of_le_of_lt hik' (by norm_num)
  have hsum : blockSum r g p x = blockSum r g p y := congrFun h1 i
  rw [blockSum_eq_single hx1, blockSum_eq_single hy1] at hsum
  have hwt : wt r (2 * k + p) x = wt r (2 * k + p) y := by simp only [wt, hr_eq]
  rw [hwt] at hsum
  have hpos : 0 < wt r (2 * k + p) y := by
    refine wt_pos ?_
    push_cast
    exact hy1
  have hgxy : g (2 * k + p) x = g (2 * k + p) y :=
    smul_right_injective (EuclideanSpace ℝ (Fin m)) (ne_of_gt hpos) hsum
  have hmem : ∀ z : M, |r z - (2 * (k : ℝ) + (p : ℝ))| ≤ 1 / 2 →
      z ∈ r ⁻¹' (Set.Icc ((((2 * k + p : ℤ)) : ℝ) - 1) ((((2 * k + p : ℤ)) : ℝ) + 1)) := by
    intro z hz
    rw [abs_le] at hz
    simp only [Set.mem_preimage, Set.mem_Icc]
    push_cast
    constructor <;> linarith [hz.1, hz.2]
  exact hginj (2 * k + p) (hmem x hik) (hmem y hik') hgxy

omit [IsManifold (𝓡 n) ∞ M] in
lemma glueMap_immersion {r : M → ℝ} (hr : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r)
    {g : ℤ → M → EuclideanSpace ℝ (Fin m)} (hg : ∀ j, ContMDiff (𝓡 n) (𝓡 m) ∞ (g j))
    (hgimm : ∀ j : ℤ, ∀ x ∈ r ⁻¹' (Set.Icc ((j : ℝ) - 1) ((j : ℝ) + 1)),
      Injective (mfderiv (𝓡 n) (𝓡 m) (g j) x)) (x : M) :
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, (Fin 2 → EuclideanSpace ℝ (Fin m)) × ℝ) (glueMap r g) x) := by
  refine (injective_iff_map_eq_zero
    (mfderiv (𝓡 n) 𝓘(ℝ, (Fin 2 → EuclideanSpace ℝ (Fin m)) × ℝ) (glueMap r g) x)).2 ?_
  intro v hv
  obtain ⟨i, k, hik⟩ := exists_block (r x)
  set p : ℤ := ((i : ℕ) : ℤ) with hp
  have hx1 : |r x - (2 * (k : ℝ) + (p : ℝ))| < 1 := lt_of_le_of_lt hik (by norm_num)
  have hΦx : HasMFDerivAt (𝓡 n) 𝓘(ℝ, (Fin 2 → EuclideanSpace ℝ (Fin m)) × ℝ) (glueMap r g) x
      (mfderiv (𝓡 n) 𝓘(ℝ, (Fin 2 → EuclideanSpace ℝ (Fin m)) × ℝ) (glueMap r g) x) :=
    ((contMDiff_glueMap hr hg x).mdifferentiableAt (by simp)).hasMFDerivAt
  have hrcomp : HasMFDerivAt (𝓡 n) 𝓘(ℝ) r x
      ((ContinuousLinearMap.snd ℝ (Fin 2 → EuclideanSpace ℝ (Fin m)) ℝ).comp
        (mfderiv (𝓡 n) 𝓘(ℝ, (Fin 2 → EuclideanSpace ℝ (Fin m)) × ℝ) (glueMap r g) x)) :=
    (ContinuousLinearMap.snd ℝ (Fin 2 → EuclideanSpace ℝ (Fin m)) ℝ).hasMFDerivAt.comp x hΦx
  have hvr : mfderiv (𝓡 n) 𝓘(ℝ) r x v = 0 := by
    rw [hrcomp.mfderiv]
    exact clm_comp_apply_zero (X := TangentSpace (𝓡 n) x) _ _ hv
  have hicomp : HasMFDerivAt (𝓡 n) (𝓡 m) (blockSum r g p) x
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => EuclideanSpace ℝ (Fin m)) i).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → EuclideanSpace ℝ (Fin m)) ℝ)).comp
        (mfderiv (𝓡 n) 𝓘(ℝ, (Fin 2 → EuclideanSpace ℝ (Fin m)) × ℝ) (glueMap r g) x)) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => EuclideanSpace ℝ (Fin m)) i).comp
      (ContinuousLinearMap.fst ℝ (Fin 2 → EuclideanSpace ℝ (Fin m)) ℝ)).hasMFDerivAt.comp x hΦx
  have hvi : mfderiv (𝓡 n) (𝓡 m) (blockSum r g p) x v = 0 := by
    rw [hicomp.mfderiv]
    exact clm_comp_apply_zero (X := TangentSpace (𝓡 n) x) _ _ hv
  have hd := mfderiv_blockSum_apply hr hg hx1 v hvr
  rw [hvi] at hd
  have hpos : 0 < wt r (2 * k + p) x := wt_pos (by push_cast; exact hx1)
  have hgv : mfderiv (𝓡 n) (𝓡 m) (g (2 * k + p)) x v = 0 := by
    rcases smul_eq_zero.1 hd.symm with h | h
    · exact absurd h (ne_of_gt hpos)
    · exact h
  have hmem : x ∈ r ⁻¹' (Set.Icc ((((2 * k + p : ℤ)) : ℝ) - 1) ((((2 * k + p : ℤ)) : ℝ) + 1)) := by
    rw [abs_le] at hik
    simp only [Set.mem_preimage, Set.mem_Icc]
    push_cast
    constructor <;> linarith [hik.1, hik.2]
  exact (injective_iff_map_eq_zero _).1 (hgimm (2 * k + p) x hmem) v hgv

end BlockGlue

open BlockGlue in
theorem solution (n m : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (r : M → ℝ) (hr : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r)
    (g : ℤ → M → EuclideanSpace ℝ (Fin m))
    (hg : ∀ j, ContMDiff (𝓡 n) (𝓡 m) ∞ (g j))
    (hginj : ∀ j : ℤ, InjOn (g j) (r ⁻¹' (Set.Icc ((j : ℝ) - 1) ((j : ℝ) + 1))))
    (hgimm : ∀ j : ℤ, ∀ x ∈ r ⁻¹' (Set.Icc ((j : ℝ) - 1) ((j : ℝ) + 1)),
      Injective (mfderiv (𝓡 n) (𝓡 m) (g j) x)) :
    ∃ (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N)),
      ContMDiff (𝓡 n) (𝓡 N) ∞ e ∧ Injective e ∧
      (∀ x, Injective (mfderiv (𝓡 n) (𝓡 N) e x)) := by
  set V := (Fin 2 → EuclideanSpace ℝ (Fin m)) × ℝ with hV
  set F := EuclideanSpace ℝ (Fin (finrank ℝ V)) with hF
  set eEF : V ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm with heEF
  refine ⟨finrank ℝ V, eEF ∘ glueMap r g,
    eEF.toDiffeomorph.contMDiff.comp (contMDiff_glueMap hr hg),
    eEF.injective.comp (glueMap_injective hginj), fun x => ?_⟩
  rw [mfderiv_comp _ eEF.differentiableAt.mdifferentiableAt
      ((contMDiff_glueMap hr hg).mdifferentiableAt (by simp)), eEF.mfderiv_eq]
  exact eEF.injective.comp (glueMap_immersion hr hg hgimm x)
