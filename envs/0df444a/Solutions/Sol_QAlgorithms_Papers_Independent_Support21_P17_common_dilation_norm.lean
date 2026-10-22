-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.common_dilation_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:23:37.95632+00:00
-- url     : https://prove2.me/submissions/2c9c6bd1-35d3-432b-865c-9054f9b88b80

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

open QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

section g71g3

variable {H G J N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N]

def g71g3_cm (f : H →L[ℂ] G) : NoiseSpace H N →L[ℂ] NoiseSpace G N :=
  ((UniformSpace.Completion.toComplL : G ⊗[ℂ] N →L[ℂ] NoiseSpace G N).comp
    (TensorProduct.mapL f (ContinuousLinearMap.id ℂ N))).extend
    (UniformSpace.Completion.toComplL : H ⊗[ℂ] N →L[ℂ] NoiseSpace H N)

lemma g71g3_dense : DenseRange (UniformSpace.Completion.toComplL : H ⊗[ℂ] N →L[ℂ] NoiseSpace H N) := by
  simpa using UniformSpace.Completion.denseRange_coe

lemma g71g3_unif : IsUniformInducing (UniformSpace.Completion.toComplL : H ⊗[ℂ] N →L[ℂ] NoiseSpace H N) := by
  simpa using UniformSpace.Completion.isUniformInducing_coe (H ⊗[ℂ] N)

lemma g71g3_cm_coe (f : H →L[ℂ] G) (x : H ⊗[ℂ] N) :
    g71g3_cm (N := N) f (x : NoiseSpace H N) =
      ((TensorProduct.mapL f (ContinuousLinearMap.id ℂ N) x : G ⊗[ℂ] N) : NoiseSpace G N) := by
  have := ContinuousLinearMap.extend_eq
    ((UniformSpace.Completion.toComplL : G ⊗[ℂ] N →L[ℂ] NoiseSpace G N).comp
      (TensorProduct.mapL f (ContinuousLinearMap.id ℂ N))) g71g3_dense g71g3_unif x
  simpa [g71g3_cm] using this

lemma g71g3_ext {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (u v : NoiseSpace H N →L[ℂ] F)
    (h : ∀ x : H ⊗[ℂ] N, u (x : NoiseSpace H N) = v x) : u = v := by
  ext z
  refine UniformSpace.Completion.induction_on z ?_ h
  exact isClosed_eq u.continuous v.continuous

lemma g71g3_cm_comp (f : H →L[ℂ] G) (g : G →L[ℂ] J) :
    (g71g3_cm (N := N) g).comp (g71g3_cm f) = g71g3_cm (g.comp f) := by
  apply g71g3_ext
  intro x
  rw [ContinuousLinearMap.comp_apply, g71g3_cm_coe, g71g3_cm_coe, g71g3_cm_coe]
  congr 1
  rw [← ContinuousLinearMap.comp_apply, ← TensorProduct.mapL_comp]
  rfl

lemma g71g3_cm_id : g71g3_cm (N := N) (ContinuousLinearMap.id ℂ H) = ContinuousLinearMap.id ℂ _ := by
  apply g71g3_ext; intro x; rw [g71g3_cm_coe]; simp

lemma g71g3_cm_zero : g71g3_cm (N := N) (0 : H →L[ℂ] G) = 0 := by
  apply g71g3_ext; intro x; rw [g71g3_cm_coe]; simp

lemma g71g3_cm_norm (f : H →L[ℂ] G) : ‖g71g3_cm (N := N) f‖ ≤ ‖f‖ := by
  have h1 := ContinuousLinearMap.opNorm_extend_le (N := 1)
    ((UniformSpace.Completion.toComplL : G ⊗[ℂ] N →L[ℂ] NoiseSpace G N).comp
      (TensorProduct.mapL f (ContinuousLinearMap.id ℂ N))) g71g3_dense
    (fun x => by simp)
  refine h1.trans ?_
  rw [NNReal.coe_one, one_mul]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h2 : ‖(UniformSpace.Completion.toComplL : G ⊗[ℂ] N →L[ℂ] NoiseSpace G N)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
  have h3 := TensorProduct.norm_mapL_le f (ContinuousLinearMap.id ℂ N)
  have h4 : ‖ContinuousLinearMap.id ℂ N‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc _ ≤ 1 * (‖f‖ * 1) := by
        gcongr
        exact h3.trans (mul_le_mul_of_nonneg_left h4 (norm_nonneg _))
    _ = ‖f‖ := by ring


def g71g3_pr (n : ℕ) (i : Fin n) : PiLp 2 (fun _ : Fin n => H) →L[ℂ] H :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n => H) i

def g71g3_inj (n : ℕ) (i : Fin n) : H →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) i)

lemma g71g3_pr_inj (n : ℕ) (i j : Fin n) :
    (g71g3_pr (H := H) n i).comp (g71g3_inj n j) =
      if j = i then ContinuousLinearMap.id ℂ H else 0 := by
  ext h
  by_cases hij : j = i
  · subst hij; simp [g71g3_pr, g71g3_inj]
  · simp [g71g3_pr, g71g3_inj, hij, Ne.symm hij]

lemma g71g3_inner_sum (n : ℕ) (z w : PiLp 2 (fun _ : Fin n => H) ⊗[ℂ] N) :
    ∑ i, inner ℂ (TensorProduct.mapL (g71g3_pr n i) (ContinuousLinearMap.id ℂ N) z)
      (TensorProduct.mapL (g71g3_pr n i) (ContinuousLinearMap.id ℂ N) w) = inner ℂ z w := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h e =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul h' e' =>
      simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul, PiLp.inner_apply,
        ContinuousLinearMap.id_apply, Finset.sum_mul]
      rfl
    | add w1 w2 ih1 ih2 => simp only [map_add, inner_add_right, Finset.sum_add_distrib, ih1, ih2]
  | add z1 z2 ih1 ih2 => simp only [map_add, inner_add_left, Finset.sum_add_distrib, ih1, ih2]

lemma g71g3_parseval (n : ℕ) (z : NoiseSpace (PiLp 2 (fun _ : Fin n => H)) N) :
    ∑ i, ‖g71g3_cm (N := N) (g71g3_pr n i) z‖ ^ 2 = ‖z‖ ^ 2 := by
  refine (g71g3_dense (H := PiLp 2 (fun _ : Fin n => H)) (N := N)).induction_on z ?_ ?_
  · apply isClosed_eq
    · have hc : ∀ i : Fin n, Continuous (fun w : NoiseSpace (PiLp 2 (fun _ : Fin n => H)) N =>
          ‖g71g3_cm (N := N) (g71g3_pr n i) w‖ ^ 2) := fun i => by fun_prop
      exact continuous_finsetSum _ fun i _ => hc i
    · exact continuous_norm.pow 2
  · intro x
    rw [UniformSpace.Completion.coe_toComplL]
    simp_rw [g71g3_cm_coe, UniformSpace.Completion.norm_coe]
    simp_rw [@norm_sq_eq_re_inner ℂ]
    rw [← map_sum, g71g3_inner_sum]

def g71g3_Psi (n : ℕ) (y : PiLp 2 (fun _ : Fin n => NoiseSpace H N)) :
    NoiseSpace (PiLp 2 (fun _ : Fin n => H)) N :=
  ∑ j, g71g3_cm (N := N) (g71g3_inj n j) (y j)

lemma g71g3_pr_Psi (n : ℕ) (y : PiLp 2 (fun _ : Fin n => NoiseSpace H N)) (i : Fin n) :
    g71g3_cm (N := N) (g71g3_pr n i) (g71g3_Psi n y) = y i := by
  rw [g71g3_Psi, map_sum]
  simp_rw [← ContinuousLinearMap.comp_apply, g71g3_cm_comp, g71g3_pr_inj]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj, g71g3_cm_zero]) (by simp)]
  simp [g71g3_cm_id]

lemma g71g3_norm_Psi (n : ℕ) (y : PiLp 2 (fun _ : Fin n => NoiseSpace H N)) :
    ‖g71g3_Psi n y‖ = ‖y‖ := by
  have h := g71g3_parseval n (g71g3_Psi n y)
  simp_rw [g71g3_pr_Psi] at h
  rw [← PiLp.norm_sq_eq_of_L2] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h.symm

lemma g71g3_KL (n : ℕ) (MM : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
    (hMM : ‖MM‖ ≤ 1) (y : PiLp 2 (fun _ : Fin n => NoiseSpace H N)) :
    ‖(WithLp.toLp 2 (fun i => ∑ j, g71g3_cm (N := N)
        ((g71g3_pr n i).comp (MM.comp (g71g3_inj n j))) (y j)) :
        PiLp 2 (fun _ : Fin n => NoiseSpace H N))‖ ≤ ‖y‖ := by
  set W := g71g3_cm (N := N) MM (g71g3_Psi n y)
  have e : ∀ i, ∑ j, g71g3_cm (N := N) ((g71g3_pr n i).comp (MM.comp (g71g3_inj n j))) (y j) =
      g71g3_cm (N := N) (g71g3_pr n i) W := by
    intro i
    simp only [W, g71g3_Psi, map_sum, ← g71g3_cm_comp, ContinuousLinearMap.comp_apply]
  simp_rw [e]
  have h1 : ‖(WithLp.toLp 2 (fun i => g71g3_cm (N := N) (g71g3_pr n i) W) :
      PiLp 2 (fun _ : Fin n => NoiseSpace H N))‖ = ‖W‖ := by
    have := g71g3_parseval n W
    rw [← PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => NoiseSpace H N)
      (WithLp.toLp 2 (fun i => g71g3_cm (N := N) (g71g3_pr n i) W))] at this
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  rw [h1]
  calc ‖W‖ ≤ ‖g71g3_cm (N := N) MM‖ * ‖g71g3_Psi n y‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖y‖ := by
        rw [g71g3_norm_Psi]
        exact mul_le_mul_of_nonneg_right ((g71g3_cm_norm MM).trans hMM) (norm_nonneg _)
    _ = ‖y‖ := one_mul _

end g71g3

lemma g71g3_diag {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℂ X]
    [NormedSpace ℂ Y] {n : ℕ} (A : X →L[ℂ] Y) (z : PiLp 2 (fun _ : Fin n => X)) :
    ‖(WithLp.toLp 2 (fun i => A (z i)) : PiLp 2 (fun _ : Fin n => Y))‖ ≤ ‖A‖ * ‖z‖ := by
  have h1 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => Y) (WithLp.toLp 2 (fun i => A (z i)))
  have h2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => X) z
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [h1, mul_pow, h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2

theorem solution (H K E : SeparableHilbertSpace) (T1 T2 : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K)
    (hT1 : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T1)
    (hT2 : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T2)
    (V1 V2 : K →L[ℂ] NoiseSpace H E)
    (hV1 : ∀ A, T1 A = compress V1 (completedTensorMap A (ContinuousLinearMap.id ℂ E)))
    (hV2 : ∀ A, T2 A = compress V2 (completedTensorMap A (ContinuousLinearMap.id ℂ E))) :
    completelyBoundedNorm (T1 - T2) ≤ (‖V1‖ + ‖V2‖) * ‖V1 - V2‖ ∧
      (IsUnitalNormalCP T1 → IsUnitalNormalCP T2 → completelyBoundedNorm (T1 - T2) ≤ 2 * ‖V1 - V2‖) := by
  have hcm : ∀ A : HilbertEndomorphism H,
      completedTensorMap A (ContinuousLinearMap.id ℂ E) = g71g3_cm (N := E) A := fun A => rfl
  have main : completelyBoundedNorm (T1 - T2) ≤ (‖V1‖ + ‖V2‖) * ‖V1 - V2‖ := by
    unfold completelyBoundedNorm
    refine Real.sSup_le ?_ (by positivity)
    rintro _ ⟨n, Mb, x, hM, hx, rfl⟩
    let MM : PiLp 2 (fun _ : Fin n => (H : Type)) →L[ℂ] PiLp 2 (fun _ : Fin n => (H : Type)) :=
      LinearMap.mkContinuous
        { toFun := applyOperatorBlocks Mb
          map_add' := fun a b => by
            ext i; simp [applyOperatorBlocks, Finset.sum_add_distrib]
          map_smul' := fun c a => by
            ext i; simp [applyOperatorBlocks, Finset.smul_sum] } 1 (fun y => by simpa using hM y)
    have hMM : ‖MM‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
    have hblk : ∀ i j, (g71g3_pr n i).comp (MM.comp (g71g3_inj n j)) = Mb i j := by
      intro i j; ext h
      simp only [ContinuousLinearMap.comp_apply, MM, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
        AddHom.coe_mk, applyOperatorBlocks, g71g3_pr, g71g3_inj]
      simp [Pi.single_apply]
      rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
      all_goals simp
    have KL := fun y => g71g3_KL (N := (E : Type)) n MM hMM y
    simp only [hblk] at KL
    set D := V1 - V2
    have hop : ∀ B : NoiseSpace H E →L[ℂ] NoiseSpace H E,
        (ContinuousLinearMap.adjoint V1).comp (B.comp V1) -
          (ContinuousLinearMap.adjoint V2).comp (B.comp V2) =
        (ContinuousLinearMap.adjoint V1).comp (B.comp D) +
          (ContinuousLinearMap.adjoint D).comp (B.comp V2) := by
      intro B
      simp only [D, map_sub, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      abel
    have hsplit : applyOperatorBlocks (fun i j => (T1 - T2) (Mb i j)) x =
        (WithLp.toLp 2 (fun i => (ContinuousLinearMap.adjoint V1)
          (∑ j, g71g3_cm (N := (E : Type)) (Mb i j) (D (x j)))) : PiLp 2 (fun _ : Fin n => (K : Type))) +
        WithLp.toLp 2 (fun i => (ContinuousLinearMap.adjoint D)
          (∑ j, g71g3_cm (N := (E : Type)) (Mb i j) (V2 (x j)))) := by
      ext i
      simp only [applyOperatorBlocks, LinearMap.sub_apply, hV1, hV2, hcm, compress, hop,
        PiLp.add_apply, PiLp.toLp_apply, map_sum, ← Finset.sum_add_distrib]
      rfl
    rw [hsplit]
    have ha := (g71g3_diag (ContinuousLinearMap.adjoint V1)
      (WithLp.toLp 2 (fun i => ∑ j, g71g3_cm (N := (E : Type)) (Mb i j) (D (x j))) :
        PiLp 2 (fun _ : Fin n => NoiseSpace H E))).trans
      (mul_le_mul_of_nonneg_left (KL (WithLp.toLp 2 (fun j => D (x j)))) (norm_nonneg _))
    have hb := (g71g3_diag (ContinuousLinearMap.adjoint D)
      (WithLp.toLp 2 (fun i => ∑ j, g71g3_cm (N := (E : Type)) (Mb i j) (V2 (x j))) :
        PiLp 2 (fun _ : Fin n => NoiseSpace H E))).trans
      (mul_le_mul_of_nonneg_left (KL (WithLp.toLp 2 (fun j => V2 (x j)))) (norm_nonneg _))
    have hDx := g71g3_diag D x
    have hVx := g71g3_diag V2 x
    simp only [PiLp.toLp_apply, LinearIsometryEquiv.norm_map] at ha hb hDx hVx
    have n1 : 0 ≤ ‖V1‖ := ContinuousLinearMap.opNorm_nonneg _
    have n2 : 0 ≤ ‖D‖ := ContinuousLinearMap.opNorm_nonneg _
    have n3 : 0 ≤ ‖V2‖ := ContinuousLinearMap.opNorm_nonneg _
    have nx : 0 ≤ ‖x‖ := norm_nonneg _
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ ‖V1‖ * (‖D‖ * ‖x‖) + ‖D‖ * (‖V2‖ * ‖x‖) := by
          gcongr
          · exact ha.trans (mul_le_mul_of_nonneg_left hDx n1)
          · exact hb.trans (mul_le_mul_of_nonneg_left hVx n2)
      _ ≤ ‖V1‖ * (‖D‖ * 1) + ‖D‖ * (‖V2‖ * 1) := by gcongr
      _ = (‖V1‖ + ‖V2‖) * ‖D‖ := by ring
  refine ⟨main, fun hu1 hu2 => main.trans ?_⟩
  have hiso : ∀ (V : K →L[ℂ] NoiseSpace H E) (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K),
      (∀ A, T A = compress V (completedTensorMap A (ContinuousLinearMap.id ℂ E))) →
      IsUnitalNormalCP T → ‖V‖ ≤ 1 := by
    intro V T hV hu
    have h1 : (ContinuousLinearMap.adjoint V).comp V = ContinuousLinearMap.id ℂ K := by
      have := hu.2
      rw [hV, hcm, g71g3_cm_id, compress] at this
      simpa using this
    have h2 := ContinuousLinearMap.norm_adjoint_comp_self V
    rw [h1] at h2
    have h3 : ‖ContinuousLinearMap.id ℂ K‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    nlinarith [ContinuousLinearMap.opNorm_nonneg V]
  have a1 := hiso V1 T1 hV1 hu1
  have a2 := hiso V2 T2 hV2 hu2
  have := ContinuousLinearMap.opNorm_nonneg (V1 - V2)
  nlinarith
