-- Prove2me | solution 1 for SpherePackingBeyond.D4_density
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:26:50.31729+00:00
-- url     : https://prove2.me/submissions/ef3cb91c-a210-49c6-aa62-04ce8e92e0ce

import Mathlib
import Definitions.Def_TenChallenges_SpherePacking
import Definitions.Def_SpherePackingBeyond_D4
set_option autoImplicit false
open scoped BigOperators
open SpherePackingBeyond
open Module MeasureTheory

/-! The `D4` packing (`√2·D4`) has density `π²/16`.
`D4centers` is the `ℤ`-span of the basis `√2·(1,-1,0,0), √2·(0,1,-1,0), √2·(0,0,1,-1), √2·(0,0,1,1)`,
of determinant `8`, so its covolume is `8`; nonzero vectors have norm `≥ 2`, so the unit balls are
disjoint. With `N(r) = #{x ∈ D4centers : ‖x‖ ≤ r}`, the union of the unit balls meets `B(0,R)` in a set
of volume between `N(R-1)·V` and `N(R+1)·V` (`V = vol B(0,1)`), and Mathlib's lattice-point count
`N(r)/r⁴ → vol(closedBall 0 1)/covolume = (π²/2)/8` gives the limit `π²/16`. -/

private def A : Matrix (Fin 4) (Fin 4) ℤ := !![1, -1, 0, 0; 0, 1, -1, 0; 0, 0, 1, -1; 0, 0, 1, 1]

private noncomputable def w (i : Fin 4) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (fun j => Real.sqrt 2 * (A i j : ℝ))

private lemma A_det : (A.map (Int.cast : ℤ → ℝ)).det = 2 := by
  simp [A, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num

private lemma det_w : (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det w = 8 := by
  rw [Module.Basis.det_apply]
  have : (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.toMatrix w =
      (Real.sqrt 2 • A.map (Int.cast : ℤ → ℝ)).transpose := by
    ext i j
    simp [Basis.toMatrix_apply, w]
  rw [this, Matrix.det_transpose, Matrix.det_smul, A_det]
  have h2 : Real.sqrt 2 ^ 4 = 4 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]; norm_num
  simp [h2]; norm_num

private lemma w_li : LinearIndependent ℝ w := by
  have := (Module.Basis.is_basis_iff_det (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis (v := w)).2
    (by rw [det_w]; exact isUnit_iff_ne_zero.2 (by norm_num))
  exact this.1

private noncomputable def b0 : Module.Basis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)) :=
  basisOfLinearIndependentOfCardEqFinrank w_li (by simp)

private lemma b0_eq : ⇑b0 = w := by simp [b0]

private noncomputable abbrev L : Submodule ℤ (EuclideanSpace ℝ (Fin 4)) :=
  Submodule.span ℤ (Set.range b0)

private lemma covol_L : ZLattice.covolume L = 8 := by
  classical
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume (b0.restrictScalars ℤ)
    (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis]
  have h1 : ((↑) ∘ (b0.restrictScalars ℤ) : Fin 4 → EuclideanSpace ℝ (Fin 4)) = w := by
    ext1 i; simp [Basis.restrictScalars_apply, b0_eq]
  rw [h1, det_w]
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume)]
  rw [measureReal_def, OrthonormalBasis.coe_toBasis, (EuclideanSpace.basisFun (Fin 4) ℝ).volume_parallelepiped]
  norm_num

private lemma w_mem (i : Fin 4) : w i ∈ D4centers := by
  refine ⟨A i, fun j => by simp [w], ?_⟩
  fin_cases i <;> simp [A, Fin.sum_univ_succ]

private lemma L_sub : (L : Set (EuclideanSpace ℝ (Fin 4))) ⊆ D4centers := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [b0_eq]; exact w_mem i
  | zero => exact ⟨0, fun j => by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨zx, hzx, hex⟩ := hx
    obtain ⟨zy, hzy, hey⟩ := hy
    refine ⟨zx + zy, fun j => ?_, ?_⟩
    · simp [hzx, hzy]; ring
    · simp only [Pi.add_apply, Finset.sum_add_distrib]; exact hex.add hey
  | smul a x _ hx =>
    obtain ⟨zx, hzx, hex⟩ := hx
    refine ⟨a • zx, fun j => ?_, ?_⟩
    · simp [hzx]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; exact hex.mul_left a

private lemma sub_L : D4centers ⊆ (L : Set (EuclideanSpace ℝ (Fin 4))) := by
  rintro x ⟨z, hz, hev⟩
  obtain ⟨k, hk⟩ := hev
  simp only [Fin.sum_univ_four] at hk
  have hx : x = z 0 • b0 0 + (z 0 + z 1) • b0 1 + (z 0 + z 1 + z 2 - k) • b0 2 + k • b0 3 := by
    ext j
    rw [b0_eq]
    have hk' : (k : ℝ) + k = z 0 + z 1 + z 2 + z 3 := by exact_mod_cast hk.symm
    have hk'' : (k : ℝ) = (z 0 + z 1 + z 2 + z 3) / 2 := by linarith
    fin_cases j <;> simp [w, A, hz, hk''] <;> ring
  rw [hx]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

private lemma L_eq : (L : Set (EuclideanSpace ℝ (Fin 4))) = D4centers :=
  Set.Subset.antisymm L_sub sub_L

private lemma norm_ge (x : EuclideanSpace ℝ (Fin 4)) (hx : x ∈ D4centers) (h0 : x ≠ 0) :
    2 ≤ ‖x‖ := by
  obtain ⟨z, hz, hev⟩ := hx
  have hz0 : z ≠ 0 := by
    rintro rfl; apply h0; ext j; simp [hz]
  have hsq : ‖x‖ ^ 2 = 2 * ((∑ i, z i ^ 2 : ℤ) : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs, hz, mul_pow, Real.sq_sqrt (by norm_num)]
  have hev2 : Even (∑ i, z i ^ 2) := by
    have : ∑ i, z i ^ 2 = ∑ i, z i + ∑ i, z i * (z i - 1) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [this]
    refine hev.add (Finset.even_sum _ fun i _ => ?_)
    exact Int.even_mul_pred_self (z i)
  have hpos : 0 < ∑ i, z i ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra hc; push Not at hc; exact hz0 (funext hc)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun j _ => sq_nonneg (z j))
      (Finset.mem_univ i))
  have h2 : (2 : ℤ) ≤ ∑ i, z i ^ 2 := by
    obtain ⟨k, hk⟩ := hev2; omega
  have : (4 : ℝ) ≤ ‖x‖ ^ 2 := by
    rw [hsq]; have : (2 : ℝ) ≤ ((∑ i, z i ^ 2 : ℤ) : ℝ) := by exact_mod_cast h2
    linarith
  nlinarith [norm_nonneg x]

private lemma dist_ge (x y : EuclideanSpace ℝ (Fin 4)) (hx : x ∈ (L : Set _)) (hy : y ∈ (L : Set _))
    (hxy : x ≠ y) : 2 ≤ dist x y := by
  rw [dist_eq_norm]
  have : x - y ∈ (L : Set _) := sub_mem hx hy
  rw [L_eq] at this
  exact norm_ge _ this (sub_ne_zero.2 hxy)

open Filter Topology Metric

private lemma vol_closedBall : volume.real (closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1) = Real.pi ^ 2 / 2 := by
  rw [measureReal_def, EuclideanSpace.volume_closedBall]
  have hg : Real.Gamma ((Fintype.card (Fin 4) : ℝ) / 2 + 1) = 2 := by
    rw [show ((Fintype.card (Fin 4) : ℝ) / 2 + 1) = ((2 : ℕ) : ℝ) + 1 by simp; norm_num,
      Real.Gamma_nat_eq_factorial]
    simp [Nat.factorial]
  rw [hg]
  have hs : Real.sqrt Real.pi ^ Fintype.card (Fin 4) = Real.pi ^ 2 := by
    rw [Fintype.card_fin, show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hs]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]

private noncomputable def K (c : ℝ) : ℕ :=
  Nat.card ({x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 4))) | ‖x‖ ^ 4 ≤ c} ∩ L :
    Set (EuclideanSpace ℝ (Fin 4)))

private lemma ball_set : {x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 4))) | ‖x‖ ^ 4 ≤ 1} =
    closedBall 0 1 := by
  ext x
  simp [pow_le_one_iff_of_nonneg (norm_nonneg x) (by norm_num : (4:ℕ) ≠ 0)]

private lemma K_tendsto : Tendsto (fun c : ℝ => (K c : ℝ) / c) atTop (𝓝 (Real.pi ^ 2 / 16)) := by
  have h := ZLattice.covolume.tendsto_card_le_div' L (X := Set.univ)
    (F := fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 4) (fun _ _ _ _ => Set.mem_univ _)
    (fun x r hr => by
      simp only [finrank_euclideanSpace_fin, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      ring)
    (by rw [ball_set]; exact isBounded_closedBall)
    (by rw [ball_set]; exact measurableSet_closedBall)
    (by rw [ball_set, frontier_closedBall _ one_ne_zero]; exact Measure.addHaar_sphere _ _ _)
  rw [ball_set, vol_closedBall, covol_L] at h
  rw [show Real.pi ^ 2 / 16 = Real.pi ^ 2 / 2 / 8 by ring]
  exact h

private lemma S_eq (r : ℝ) (hr : 0 ≤ r) :
    ({x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 4))) | ‖x‖ ^ 4 ≤ r ^ 4} ∩ L :
      Set (EuclideanSpace ℝ (Fin 4))) = closedBall 0 r ∩ L := by
  ext x
  simp [pow_le_pow_iff_left₀ (norm_nonneg x) hr (by norm_num : (4:ℕ) ≠ 0)]

private lemma S_fin (r : ℝ) : (closedBall (0 : EuclideanSpace ℝ (Fin 4)) r ∩ L).Finite :=
  ZSpan.setFinite_inter b0 isBounded_closedBall

private lemma K_eq (r : ℝ) (hr : 0 ≤ r) : K (r ^ 4) = (S_fin r).toFinset.card := by
  rw [K, S_eq r hr, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (S_fin r)]

private noncomputable def V : ENNReal := volume (ball (0 : EuclideanSpace ℝ (Fin 4)) 1)

private lemma V_ne_zero : V ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
private lemma V_ne_top : V ≠ ⊤ := measure_ball_lt_top.ne

private lemma vol_ball (x : EuclideanSpace ℝ (Fin 4)) : volume (ball x 1) = V :=
  Measure.addHaar_ball_center volume x 1

private lemma lower (R : ℝ) (hR : 1 ≤ R) :
    (K ((R - 1) ^ 4) : ENNReal) * V ≤
      volume ((⋃ x ∈ D4centers, ball x 1) ∩ ball (0 : EuclideanSpace ℝ (Fin 4)) R) := by
  rw [K_eq _ (by linarith)]
  set T := (S_fin (R - 1)).toFinset
  have hsub : (⋃ x ∈ T, ball x 1) ⊆ (⋃ x ∈ D4centers, ball x 1) ∩ ball 0 R := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hxT, hz⟩ := hz
    rw [Set.Finite.mem_toFinset] at hxT
    refine ⟨Set.mem_biUnion (L_sub hxT.2) hz, ?_⟩
    have h1 : ‖x‖ ≤ R - 1 := by simpa using hxT.1
    have h2 : dist z x < 1 := hz
    rw [mem_ball_zero_iff]
    calc ‖z‖ ≤ ‖z - x‖ + ‖x‖ := norm_le_norm_sub_add z x
      _ < 1 + (R - 1) := by rw [← dist_eq_norm]; linarith
      _ = R := by ring
  have hdisj : (T : Set (EuclideanSpace ℝ (Fin 4))).PairwiseDisjoint (fun x => ball x 1) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, T] at hx hy
    exact ball_disjoint_ball (by have := dist_ge x y hx.2 hy.2 hxy; linarith)
  calc (T.card : ENNReal) * V = ∑ x ∈ T, volume (ball x 1) := by
        simp [vol_ball]
    _ = volume (⋃ x ∈ T, ball x 1) :=
        (measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)).symm
    _ ≤ _ := measure_mono hsub

private lemma upper (R : ℝ) (hR : 0 ≤ R) :
    volume ((⋃ x ∈ D4centers, ball x 1) ∩ ball (0 : EuclideanSpace ℝ (Fin 4)) R) ≤
      (K ((R + 1) ^ 4) : ENNReal) * V := by
  rw [K_eq _ (by linarith)]
  set T := (S_fin (R + 1)).toFinset
  have hsub : (⋃ x ∈ D4centers, ball x 1) ∩ ball 0 R ⊆ (⋃ x ∈ T, ball x 1) := by
    rintro z ⟨hz, hzR⟩
    simp only [Set.mem_iUnion] at hz ⊢
    obtain ⟨x, hxC, hz⟩ := hz
    refine ⟨x, ?_, hz⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, sub_L hxC⟩
    rw [mem_closedBall_zero_iff]
    rw [mem_ball_zero_iff] at hzR
    have h2 : dist z x < 1 := hz
    rw [dist_eq_norm] at h2
    calc ‖x‖ ≤ ‖x - z‖ + ‖z‖ := norm_le_norm_sub_add x z
      _ ≤ 1 + R := by rw [norm_sub_rev]; linarith
      _ = R + 1 := by ring
  calc volume ((⋃ x ∈ D4centers, ball x 1) ∩ ball (0 : EuclideanSpace ℝ (Fin 4)) R)
      ≤ volume (⋃ x ∈ T, ball x 1) := measure_mono hsub
    _ ≤ ∑ x ∈ T, volume (ball x 1) := measure_biUnion_finset_le _ _
    _ = (T.card : ENNReal) * V := by simp [vol_ball]

private lemma ratio (k : ℕ) (R : ℝ) (hR : 0 < R) :
    (k : ENNReal) * V / volume (ball (0 : EuclideanSpace ℝ (Fin 4)) R) =
      ENNReal.ofReal ((k : ℝ) / R ^ 4) := by
  rw [Measure.addHaar_ball_of_pos volume _ hR, finrank_euclideanSpace_fin]
  rw [← V, ENNReal.mul_div_mul_right _ _ V_ne_zero V_ne_top,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast]

private lemma lim_low : Tendsto (fun R : ℝ => (K ((R - 1) ^ 4) : ℝ) / R ^ 4) atTop
    (𝓝 (Real.pi ^ 2 / 16)) := by
  have h1 : Tendsto (fun R : ℝ => (R - 1) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  have h2 : Tendsto (fun R : ℝ => (1 - R⁻¹) ^ 4) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1:ℝ))).sub tendsto_inv_atTop_zero).pow 4
    simpa using this
  have := (K_tendsto.comp h1).mul h2
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with R hR
  have : R - 1 ≠ 0 := by linarith
  have : R ≠ 0 := by linarith
  simp only [Function.comp_apply]
  field_simp

private lemma lim_up : Tendsto (fun R : ℝ => (K ((R + 1) ^ 4) : ℝ) / R ^ 4) atTop
    (𝓝 (Real.pi ^ 2 / 16)) := by
  have h1 : Tendsto (fun R : ℝ => (R + 1) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  have h2 : Tendsto (fun R : ℝ => (1 + R⁻¹) ^ 4) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1:ℝ))).add tendsto_inv_atTop_zero).pow 4
    simpa using this
  have := (K_tendsto.comp h1).mul h2
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with R hR
  have : R + 1 ≠ 0 := by linarith
  have : R ≠ 0 := by linarith
  simp only [Function.comp_apply]
  field_simp

theorem solution : upperDensity D4centers = ENNReal.ofReal (Real.pi ^ 2 / 16) := by
  unfold upperDensity
  refine Tendsto.limsup_eq ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (ENNReal.tendsto_ofReal lim_low)
    (ENNReal.tendsto_ofReal lim_up) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with R hR
    rw [← ratio _ _ (by linarith)]
    exact ENNReal.div_le_div_right (lower R hR) _
  · filter_upwards [eventually_ge_atTop 1] with R hR
    rw [← ratio _ _ (by linarith)]
    exact ENNReal.div_le_div_right (upper R (by linarith)) _
