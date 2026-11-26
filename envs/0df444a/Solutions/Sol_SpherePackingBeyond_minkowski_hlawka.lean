-- Prove2me | solution 1 for SpherePackingBeyond.minkowski_hlawka
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-26T22:07:40.030839+00:00
-- url     : https://prove2.me/submissions/a9964e4d-d19b-41b8-8e1b-a0affe31f5c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TenChallenges_SpherePacking
import Definitions.Def_SpherePackingBeyond_D4
import Theorems.Thm_LefebvreVariations_minkowski_hlawka_unimodular_ball
set_option autoImplicit false
open scoped BigOperators
open Module MeasureTheory Filter Topology Metric
open SpherePackingBeyond

/-! Reduction of the open milestone `SpherePackingBeyond.minkowski_hlawka` (`Δᴸ_d ≥ ζ(d)/2^{d-1}`) to the
variation `LefebvreVariations.minkowski_hlawka_unimodular_ball` (Hlawka 1943, geometry-of-numbers form:
a unimodular lattice with no nonzero point in a ball of volume `< 2ζ(d)`).
Everything else is proved here: `lattice_density` (a lattice packing with minimal distance `≥ 2` has
upper density `vol B(0,1)/covolume`, by Mathlib's lattice-point count `N(r)/r^d → vol/covol`), the
scaling of a basis by `2/ρ`, and the limit `ρ ↗ ρ₀` where `vol B(0,ρ₀) = 2ζ(d)`.
`#print axioms solution` shows `the gap axiom` only through the variation (the only open step of this file).
Imported `Theorems.Thm_SpherePackingBeyond_minkowski_hlawka` is used only for the `type_of%` check. -/

open LefebvreVariations

namespace Red
variable {d : ℕ}

private noncomputable def K (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (c : ℝ) : ℕ :=
  Nat.card ({x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) | ‖x‖ ^ d ≤ c} ∩ L :
    Set (EuclideanSpace ℝ (Fin d)))

noncomputable def V (d : ℕ) : ENNReal := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)

lemma V_ne_zero : V d ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
lemma V_ne_top : V d ≠ ⊤ := measure_ball_lt_top.ne

private lemma vol_ball (x : EuclideanSpace ℝ (Fin d)) : volume (ball x 1) = V d :=
  Measure.addHaar_ball_center volume x 1

private lemma vol_closedBall (d : ℕ) :
    volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) = (V d).toReal := by
  rw [measureReal_def, Measure.addHaar_closedBall volume _ zero_le_one]
  simp [V]

private lemma ball_set (hd : d ≠ 0) :
    {x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) | ‖x‖ ^ d ≤ 1} = closedBall 0 1 := by
  ext x
  simp [pow_le_one_iff_of_nonneg (norm_nonneg x) hd]

private lemma K_tendsto (hd : d ≠ 0) (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    Tendsto (fun c : ℝ => (K L c : ℝ) / c) atTop (𝓝 ((V d).toReal / ZLattice.covolume L)) := by
  have : NeZero d := ⟨hd⟩
  have h := ZLattice.covolume.tendsto_card_le_div' L (X := Set.univ)
    (F := fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ d) (fun _ _ _ _ => Set.mem_univ _)
    (fun x r hr => by
      simp only [finrank_euclideanSpace_fin, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      rw [mul_pow])
    (by rw [ball_set hd]; exact isBounded_closedBall)
    (by rw [ball_set hd]; exact measurableSet_closedBall)
    (by rw [ball_set hd, frontier_closedBall _ one_ne_zero]; exact Measure.addHaar_sphere _ _ _)
  rw [ball_set hd, vol_closedBall] at h
  exact h

private lemma S_eq (hd : d ≠ 0) (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (r : ℝ) (hr : 0 ≤ r) :
    ({x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) | ‖x‖ ^ d ≤ r ^ d} ∩ L :
      Set (EuclideanSpace ℝ (Fin d))) = closedBall 0 r ∩ L := by
  ext x
  simp [pow_le_pow_iff_left₀ (norm_nonneg x) hr hd]

private lemma S_fin (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L]
    [IsZLattice ℝ L] (r : ℝ) : (closedBall (0 : EuclideanSpace ℝ (Fin d)) r ∩ L).Finite := by
  have h := ZSpan.setFinite_inter ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
    (s := closedBall (0 : EuclideanSpace ℝ (Fin d)) r) isBounded_closedBall
  rwa [Basis.ofZLatticeBasis_span] at h

private lemma K_eq (hd : d ≠ 0) (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L]
    [IsZLattice ℝ L] (r : ℝ) (hr : 0 ≤ r) : K L (r ^ d) = (S_fin L r).toFinset.card := by
  rw [K, S_eq hd L r hr, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (S_fin L r)]

private lemma lower (hd : d ≠ 0) (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → 2 ≤ dist x y) (R : ℝ) (hR : 1 ≤ R) :
    (K L ((R - 1) ^ d) : ENNReal) * V d ≤
      volume ((⋃ x ∈ (L : Set (EuclideanSpace ℝ (Fin d))), ball x 1) ∩
        ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  rw [K_eq hd L _ (by linarith)]
  set T := (S_fin L (R - 1)).toFinset
  have hsub : (⋃ x ∈ T, ball x 1) ⊆ (⋃ x ∈ (L : Set (EuclideanSpace ℝ (Fin d))), ball x 1) ∩
      ball 0 R := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hxT, hz⟩ := hz
    rw [Set.Finite.mem_toFinset] at hxT
    refine ⟨Set.mem_biUnion hxT.2 hz, ?_⟩
    have h1 : ‖x‖ ≤ R - 1 := by simpa using hxT.1
    have h2 : dist z x < 1 := hz
    rw [mem_ball_zero_iff]
    calc ‖z‖ ≤ ‖z - x‖ + ‖x‖ := norm_le_norm_sub_add z x
      _ < 1 + (R - 1) := by rw [← dist_eq_norm]; linarith
      _ = R := by ring
  have hdisj : (T : Set (EuclideanSpace ℝ (Fin d))).PairwiseDisjoint (fun x => ball x 1) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, T] at hx hy
    exact ball_disjoint_ball (by have := hL x hx.2 y hy.2 hxy; linarith)
  calc (T.card : ENNReal) * V d = ∑ x ∈ T, volume (ball x 1) := by
        simp [vol_ball]
    _ = volume (⋃ x ∈ T, ball x 1) :=
        (measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)).symm
    _ ≤ _ := measure_mono hsub

private lemma upper (hd : d ≠ 0) (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L]
    [IsZLattice ℝ L] (R : ℝ) (hR : 0 ≤ R) :
    volume ((⋃ x ∈ (L : Set (EuclideanSpace ℝ (Fin d))), ball x 1) ∩
        ball (0 : EuclideanSpace ℝ (Fin d)) R) ≤ (K L ((R + 1) ^ d) : ENNReal) * V d := by
  rw [K_eq hd L _ (by linarith)]
  set T := (S_fin L (R + 1)).toFinset
  have hsub : (⋃ x ∈ (L : Set (EuclideanSpace ℝ (Fin d))), ball x 1) ∩ ball 0 R ⊆
      (⋃ x ∈ T, ball x 1) := by
    rintro z ⟨hz, hzR⟩
    simp only [Set.mem_iUnion] at hz ⊢
    obtain ⟨x, hxC, hz⟩ := hz
    refine ⟨x, ?_, hz⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, hxC⟩
    rw [mem_closedBall_zero_iff]
    rw [mem_ball_zero_iff] at hzR
    have h2 : dist z x < 1 := hz
    rw [dist_eq_norm] at h2
    calc ‖x‖ ≤ ‖x - z‖ + ‖z‖ := norm_le_norm_sub_add x z
      _ ≤ 1 + R := by rw [norm_sub_rev]; linarith
      _ = R + 1 := by ring
  calc volume ((⋃ x ∈ (L : Set (EuclideanSpace ℝ (Fin d))), ball x 1) ∩
        ball (0 : EuclideanSpace ℝ (Fin d)) R)
      ≤ volume (⋃ x ∈ T, ball x 1) := measure_mono hsub
    _ ≤ ∑ x ∈ T, volume (ball x 1) := measure_biUnion_finset_le _ _
    _ = (T.card : ENNReal) * V d := by simp [vol_ball]

private lemma ratio (k : ℕ) (R : ℝ) (hR : 0 < R) :
    (k : ENNReal) * V d / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) =
      ENNReal.ofReal ((k : ℝ) / R ^ d) := by
  rw [Measure.addHaar_ball_of_pos volume _ hR, finrank_euclideanSpace_fin]
  rw [← V, ENNReal.mul_div_mul_right _ _ V_ne_zero V_ne_top,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast]

private lemma lim_low (hd : d ≠ 0) (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    Tendsto (fun R : ℝ => (K L ((R - 1) ^ d) : ℝ) / R ^ d) atTop
      (𝓝 ((V d).toReal / ZLattice.covolume L)) := by
  have h1 : Tendsto (fun R : ℝ => (R - 1) ^ d) atTop atTop :=
    (tendsto_pow_atTop hd).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  have h2 : Tendsto (fun R : ℝ => (1 - R⁻¹) ^ d) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1:ℝ))).sub tendsto_inv_atTop_zero).pow d
    simpa using this
  have := (K_tendsto hd L |>.comp h1).mul h2
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with R hR
  have : R - 1 ≠ 0 := by linarith
  have : R ≠ 0 := by linarith
  simp only [Function.comp_apply]
  have e : (1 - R⁻¹) = (R - 1) / R := by field_simp
  rw [e, div_pow]
  field_simp

private lemma lim_up (hd : d ≠ 0) (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    Tendsto (fun R : ℝ => (K L ((R + 1) ^ d) : ℝ) / R ^ d) atTop
      (𝓝 ((V d).toReal / ZLattice.covolume L)) := by
  have h1 : Tendsto (fun R : ℝ => (R + 1) ^ d) atTop atTop :=
    (tendsto_pow_atTop hd).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  have h2 : Tendsto (fun R : ℝ => (1 + R⁻¹) ^ d) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1:ℝ))).add tendsto_inv_atTop_zero).pow d
    simpa using this
  have := (K_tendsto hd L |>.comp h1).mul h2
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with R hR
  have : R + 1 ≠ 0 := by linarith
  have : R ≠ 0 := by linarith
  simp only [Function.comp_apply]
  have e : (1 + R⁻¹) = (R + 1) / R := by field_simp
  rw [e, div_pow]
  field_simp

/-- A lattice packing (unit balls at the points of a full `ℤ`-lattice `L` with all mutual
distances `≥ 2`) has density `vol B(0,1) / covol L`. -/
theorem lattice_density (hd : d ≠ 0) (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology L] [IsZLattice ℝ L] (hL : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → 2 ≤ dist x y) :
    upperDensity (L : Set (EuclideanSpace ℝ (Fin d))) =
      ENNReal.ofReal ((V d).toReal / ZLattice.covolume L) := by
  unfold upperDensity
  refine Tendsto.limsup_eq ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (ENNReal.tendsto_ofReal (lim_low hd L))
    (ENNReal.tendsto_ofReal (lim_up hd L)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with R hR
    rw [← ratio _ _ (by linarith)]
    exact ENNReal.div_le_div_right (lower hd L hL R hR) _
  · filter_upwards [eventually_ge_atTop 1] with R hR
    rw [← ratio _ _ (by linarith)]
    exact ENNReal.div_le_div_right (upper hd L R (by linarith)) _


private lemma scale_apply {d : ℕ} (b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) {c : ℝ}
    (hc : c ≠ 0) (i : Fin d) :
    (b.unitsSMul (fun _ => Units.mk0 c hc)) i = c • b i := by
  rw [Module.Basis.unitsSMul_apply]; rfl

private lemma toMatrix_scale {d : ℕ} (b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) {c : ℝ}
    (hc : c ≠ 0) :
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det (b.unitsSMul (fun _ => Units.mk0 c hc)) =
      c ^ d * (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det b := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  have : (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.toMatrix
      (b.unitsSMul (fun _ => Units.mk0 c hc)) =
      c • (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.toMatrix b := by
    ext i j
    simp [Module.Basis.toMatrix_apply, scale_apply]
  rw [this, Matrix.det_smul]
  simp

private lemma covol_span {d : ℕ} (b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) =
      |(EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det b| := by
  classical
  rw [ZLattice.covolume_eq_det_mul_measureReal _ volume (b.restrictScalars ℤ)
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
  have h1 : ((↑) ∘ (b.restrictScalars ℤ) : Fin d → EuclideanSpace ℝ (Fin d)) = b := by
    ext1 i; simp [Module.Basis.restrictScalars_apply]
  rw [h1]
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume)]
  rw [measureReal_def, OrthonormalBasis.coe_toBasis,
    (EuclideanSpace.basisFun (Fin d) ℝ).volume_parallelepiped]
  simp

/-- The density of the lattice packing from a basis `b` whose lattice has minimum `≥ ρ`, scaled by `2/ρ`. -/
private lemma density_of_basis {d : ℕ} (hd : d ≠ 0) (ρ : ℝ) (hρ : 0 < ρ)
    (b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (hdet : |(EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det b| = 1)
    (hmin : ∀ z : Fin d → ℤ, z ≠ 0 → ρ ≤ ‖∑ i, z i • b i‖) :
    ENNReal.ofReal (volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) ρ) / 2 ^ d) ≤
      latticePackingConstant d := by
  have hc : (2 / ρ) ≠ 0 := by positivity
  set b' := b.unitsSMul (fun _ => Units.mk0 (2 / ρ) hc) with hb'
  set L : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℤ (Set.range b') with hL
  have hb'i : ∀ i, b' i = (2 / ρ) • b i := by
    intro i; rw [hb']; exact scale_apply b hc i
  have hsep : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → 2 ≤ dist x y := by
    intro x hx y hy hxy
    have hm : x - y ∈ L := sub_mem hx hy
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hm
    have hz0 : z ≠ 0 := by
      rintro rfl
      apply hxy
      have : x - y = 0 := by rw [← hz]; simp
      exact sub_eq_zero.1 this
    have h1 : ∑ i, z i • b' i = (2 / ρ) • ∑ i, z i • b i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb'i, smul_comm]
    rw [dist_eq_norm, ← hz, h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc (2 : ℝ) = 2 / ρ * ρ := by field_simp
      _ ≤ 2 / ρ * ‖∑ i, z i • b i‖ :=
        mul_le_mul_of_nonneg_left (hmin z hz0) (by positivity)
  have hdens := lattice_density hd L hsep
  have hcov : ZLattice.covolume L = (2 / ρ) ^ d := by
    rw [hL, covol_span, hb', toMatrix_scale b hc, abs_mul, hdet, mul_one,
      abs_of_pos (by positivity)]
  have hvol : volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) ρ) = ρ ^ d * (V d).toReal := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume _ hρ, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rfl
  have heq : (V d).toReal / ZLattice.covolume L = volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) ρ) / 2 ^ d := by
    rw [hcov, hvol, div_pow]
    field_simp
  have hspan : Submodule.span ℝ ((L.toAddSubgroup : AddSubgroup (EuclideanSpace ℝ (Fin d))) :
      Set (EuclideanSpace ℝ (Fin d))) = ⊤ := by
    change Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin d))) = ⊤
    rw [hL, Submodule.span_span_of_tower, b'.span_eq]
  calc ENNReal.ofReal (volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) ρ) / 2 ^ d)
      = upperDensity (L : Set (EuclideanSpace ℝ (Fin d))) := by rw [hdens, heq]
    _ ≤ latticePackingConstant d := by
      unfold latticePackingConstant
      exact le_iSup₂_of_le (f := fun (L : AddSubgroup (EuclideanSpace ℝ (Fin d)))
        (_ : IsUnitPacking (L : PointSet d)) => ⨆ (_ : Submodule.span ℝ (L : PointSet d) = ⊤),
          upperDensity (L : PointSet d)) L.toAddSubgroup
        (fun x hx y hy hxy => hsep x hx y hy hxy) (le_iSup_of_le hspan le_rfl)

end Red

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ENNReal.ofReal ((∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ) ^ d)) / (2 : ℝ) ^ (d - 1)) ≤ latticePackingConstant d := by
  set Z : ℝ := ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ) ^ d) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  rcases hZ0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  have hd0 : d ≠ 0 := by omega
  have hV : 0 < (Red.V d).toReal := ENNReal.toReal_pos Red.V_ne_zero Red.V_ne_top
  set ρ0 : ℝ := (2 * Z / (Red.V d).toReal) ^ ((d : ℝ)⁻¹) with hρ0
  have hρ0pos : 0 < ρ0 := Real.rpow_pos_of_pos (by positivity) _
  have hρ0d : ρ0 ^ d = 2 * Z / (Red.V d).toReal := by
    rw [hρ0, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      inv_mul_cancel₀ (by exact_mod_cast hd0), Real.rpow_one]
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      ENNReal.ofReal (Z * t ^ d / 2 ^ (d - 1)) ≤ latticePackingConstant d := by
    intro t ht0 ht1
    have hρ : 0 < t * ρ0 := by positivity
    have hvol : volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) (t * ρ0)) =
        t ^ d * (2 * Z) := by
      rw [measureReal_def, Measure.addHaar_ball_of_pos volume _ hρ, finrank_euclideanSpace_fin,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), mul_pow, hρ0d]
      change t ^ d * (2 * Z / (Red.V d).toReal) * (Red.V d).toReal = _
      field_simp
    have hlt : volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) (t * ρ0)) < 2 * Z := by
      rw [hvol]
      have : t ^ d < 1 := pow_lt_one₀ ht0.le ht1 hd0
      nlinarith
    obtain ⟨b, hdet, hmin⟩ := LefebvreVariations.minkowski_hlawka_unimodular_ball d hd _ hρ hlt
    refine le_trans (le_of_eq ?_) (Red.density_of_basis hd0 _ hρ b hdet hmin)
    congr 1
    rw [hvol]
    have : (2 : ℝ) ^ d = 2 * 2 ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; field_simp
  have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (Z * t ^ d / 2 ^ (d - 1))) (𝓝[<] 1)
      (𝓝 (ENNReal.ofReal (Z / 2 ^ (d - 1)))) := by
    have hc : Continuous (fun t : ℝ => Z * t ^ d / 2 ^ (d - 1)) := by fun_prop
    have h := ((ENNReal.continuous_ofReal.comp hc).tendsto 1).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simp only [Function.comp_def, one_pow, mul_one] at h
    exact h
  exact le_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht using
      key t ht.1 ht.2)
