-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P50.gauge_transformations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:44:21.699515+00:00
-- url     : https://prove2.me/submissions/7fdbb1da-ec80-4944-aa3f-399b03b8684d

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P50
noncomputable section

open QAlgorithms.Papers.Independent.Claimed50.P50

open scoped TensorProduct BigOperators

variable {H N : Type*}

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]

lemma g68m_ctm_coe (A : H →L[ℂ] H) (B : N →L[ℂ] N) (t : TensorProduct ℂ H N) :
    completedTensorMap A B (t : NoiseSpace H N) =
      ((TensorProduct.mapL A B t : TensorProduct ℂ H N) : NoiseSpace H N) := by
  unfold completedTensorMap
  have h := ContinuousLinearMap.extend_eq
    ((UniformSpace.Completion.toComplL :
      TensorProduct ℂ H N →L[ℂ] NoiseSpace H N).comp (TensorProduct.mapL A B))
    (e := (UniformSpace.Completion.toComplL : TensorProduct ℂ H N →L[ℂ] NoiseSpace H N))
    UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) t
  simpa using h

lemma g68m_ctm_tmul (A : H →L[ℂ] H) (B : N →L[ℂ] N) (h : H) (n : N) :
    completedTensorMap A B ((h ⊗ₜ[ℂ] n : TensorProduct ℂ H N) : NoiseSpace H N) =
      ((A h ⊗ₜ[ℂ] B n : TensorProduct ℂ H N) : NoiseSpace H N) := by
  rw [g68m_ctm_coe]; rfl

lemma g68m_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F G : NoiseSpace H N →L[ℂ] E)
    (hFG : ∀ (h : H) (n : N), F ((h ⊗ₜ[ℂ] n : TensorProduct ℂ H N) : NoiseSpace H N) =
      G ((h ⊗ₜ[ℂ] n : TensorProduct ℂ H N) : NoiseSpace H N)) : F = G := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq F.continuous G.continuous
  | ih t =>
    induction t using TensorProduct.induction_on with
    | zero => rw [UniformSpace.Completion.coe_zero, map_zero, map_zero]
    | tmul h n => exact hFG h n
    | add x y hx hy => rw [UniformSpace.Completion.coe_add, map_add, map_add, hx, hy]

lemma g68m_ins_apply (a : N) (h : H) :
    noiseInsertion a h = ((h ⊗ₜ[ℂ] a : TensorProduct ℂ H N) : NoiseSpace H N) := rfl

lemma g68m_inner_ins (a a' : N) (h h' : H) :
    inner ℂ (noiseInsertion (H := H) a h) (noiseInsertion a' h') = inner ℂ h h' * inner ℂ a a' := by
  rw [g68m_ins_apply, g68m_ins_apply, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]

lemma g68m_ins_add (a a' : N) (h : H) :
    noiseInsertion (H := H) (a + a') h = noiseInsertion a h + noiseInsertion a' h := by
  simp only [g68m_ins_apply, TensorProduct.tmul_add, UniformSpace.Completion.coe_add]

lemma g68m_ins_zero (h : H) : noiseInsertion (H := H) (0 : N) h = 0 := by
  simp only [g68m_ins_apply, TensorProduct.tmul_zero, UniformSpace.Completion.coe_zero]

lemma g68m_rot_ins (g : NoiseGauge N) (a : N) (h : H) :
    noiseRotation g (noiseInsertion a h) = noiseInsertion (g.Dnoise a) h := by
  rw [g68m_ins_apply, noiseRotation, g68m_ctm_tmul]; rfl

lemma g68m_X_ins (X : H →L[ℂ] H) (a : N) (h : H) :
    completedTensorMap X (ContinuousLinearMap.id ℂ N) (noiseInsertion a h) =
      noiseInsertion a (X h) := by
  rw [g68m_ins_apply, g68m_ctm_tmul]; rfl

lemma g68m_rot_comm (g : NoiseGauge N) (X : H →L[ℂ] H) :
    (noiseRotation g).comp (completedTensorMap X (ContinuousLinearMap.id ℂ N)) =
      (completedTensorMap X (ContinuousLinearMap.id ℂ N)).comp (noiseRotation (H := H) g) := by
  apply g68m_ext; intro h n
  simp only [ContinuousLinearMap.comp_apply, noiseRotation, g68m_ctm_tmul]; rfl

lemma g68m_rot_mul (gp g : NoiseGauge N) :
    (noiseRotation gp).comp (noiseRotation g) = noiseRotation (H := H) (gaugeMul gp g) := by
  apply g68m_ext; intro h n
  simp only [ContinuousLinearMap.comp_apply, noiseRotation, g68m_ctm_tmul]; rfl

lemma g68m_rot_id : noiseRotation (H := H) (gaugeIdentity (N := N)) = ContinuousLinearMap.id ℂ _ := by
  apply g68m_ext; intro h n
  simp only [noiseRotation, g68m_ctm_tmul]; rfl

lemma g68m_rot_norm (g : NoiseGauge N) (x : NoiseSpace H N) : ‖noiseRotation g x‖ = ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (noiseRotation g).continuous) continuous_norm
  | ih t =>
    rw [noiseRotation, g68m_ctm_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    have := TensorProduct.norm_map (LinearIsometry.id (R := ℂ) (E := H))
      g.Dnoise.toLinearIsometry t
    rw [TensorProduct.mapL_apply]; exact this

lemma g68m_rot_inner (g : NoiseGauge N) (x y : NoiseSpace H N) :
    inner ℂ (noiseRotation g x) (noiseRotation g y) = inner ℂ x y := by
  let R : NoiseSpace H N →ₗᵢ[ℂ] NoiseSpace H N :=
    ⟨(noiseRotation g).toLinearMap, fun x => g68m_rot_norm g x⟩
  exact R.inner_map_map x y

lemma g68m_ins_X_inner (X : H →L[ℂ] H) (a : N) (h : H) (y : NoiseSpace H N) :
    inner ℂ (noiseInsertion a h) (completedTensorMap X (ContinuousLinearMap.id ℂ N) y) =
      inner ℂ (noiseInsertion a (X.adjoint h)) y := by
  have := g68m_ext ((innerSL ℂ (noiseInsertion a h)).comp
      (completedTensorMap X (ContinuousLinearMap.id ℂ N)))
    (innerSL ℂ (noiseInsertion a (X.adjoint h))) (fun h' n' => by
      simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, g68m_ctm_tmul, g68m_ins_apply,
        UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul,
        ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.id_apply])
  simpa using congrArg (fun F => F y) this


lemma g68m_gauge_ext {g g' : NoiseGauge N} (hD : g.Dnoise = g'.Dnoise) (ha : g.a = g'.a)
    (hb : g.b = g'.b) : g = g' := by
  cases g; cases g'; simp_all

lemma g68m_sd_ext {D : Submodule ℂ H} {S S' : StandardData (N := N) D} (hL : S.L = S'.L)
    (hK : S.K = S'.K) : S = S' := by
  cases S; cases S'; simp_all

lemma g68m_GL {D : Submodule ℂ H} (g : NoiseGauge N) (S : StandardData (N := N) D) (psi : D) :
    (gaugeAction g S).L psi = noiseRotation g (S.L psi) + noiseInsertion g.a (psi : H) := rfl

lemma g68m_inner_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

lemma g68m_GK {D : Submodule ℂ H} (g : NoiseGauge N) (S : StandardData (N := N) D) (psi : D) :
    (gaugeAction g S).K psi = S.K psi + (noiseInsertion g.a).adjoint (noiseRotation g (S.L psi)) +
      ((((‖g.a‖ ^ 2 / 2 : ℝ) : ℂ) - Complex.I * (g.b : ℂ)) • (psi : H)) := rfl

lemma g68m_conj_c (a : N) (b : ℝ) :
    (starRingEnd ℂ) (((‖a‖ ^ 2 / 2 : ℝ) : ℂ) - Complex.I * (b : ℂ)) =
      ((‖a‖ ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (b : ℂ) := by
  rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring

lemma g68m_form {D : Submodule ℂ H} (g : NoiseGauge N) (S : StandardData (N := N) D)
    (psi : D) (X : H →L[ℂ] H) (phi : D) :
    standardForm (gaugeAction g S) psi X phi = standardForm S psi X phi := by
  set R := noiseRotation (H := H) g
  set XI := completedTensorMap X (ContinuousLinearMap.id ℂ N)
  set J := noiseInsertion (H := H) g.a
  set u := S.L psi
  set v := S.L phi
  set p := (psi : H)
  set q := (phi : H)
  have e1 : inner ℂ (R u) (XI (R v)) = inner ℂ u (XI v) := by
    rw [← ContinuousLinearMap.comp_apply XI R, ← g68m_rot_comm, ContinuousLinearMap.comp_apply,
      g68m_rot_inner]
  have e2 : inner ℂ (R u) (XI (J q)) = inner ℂ (J.adjoint (R u)) (X q) := by
    rw [g68m_X_ins, ContinuousLinearMap.adjoint_inner_left]
  have e3 : inner ℂ (J p) (XI (R v)) = inner ℂ p (X (J.adjoint (R v))) := by
    rw [g68m_ins_X_inner, ← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_left]
  have e4 : inner ℂ (J p) (XI (J q)) = inner ℂ p (X q) * ((‖g.a‖ ^ 2 : ℝ) : ℂ) := by
    rw [g68m_X_ins, g68m_inner_ins, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp only [standardForm, g68m_GL, g68m_GK]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, map_add, map_add,
    inner_add_left, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
    map_smul, inner_smul_right, e1, e2, e3, e4, g68m_conj_c]
  change _ = inner ℂ u (XI v) - _ - _
  push_cast
  ring

lemma g68m_diss {D : Submodule ℂ H} (g : NoiseGauge N) (S : StandardData (N := N) D)
    (hDiss : IsDissipative S) : IsDissipative (gaugeAction g S) := by
  intro psi
  have h0 := hDiss psi
  rw [g68m_GL, g68m_GK]
  set R := noiseRotation (H := H) g
  set J := noiseInsertion (H := H) g.a
  set u := S.L psi
  set p := (psi : H)
  have hn : ‖J p‖ ^ 2 = ‖p‖ ^ 2 * ‖g.a‖ ^ 2 := by
    rw [g68m_ins_apply, UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul, mul_pow]
  have hadj : inner ℂ p (J.adjoint (R u)) = inner ℂ (J p) (R u) :=
    ContinuousLinearMap.adjoint_inner_right _ _ _
  rw [@norm_add_sq ℂ, g68m_rot_norm, hn, inner_add_right, inner_add_right, inner_smul_right, hadj,
    g68m_inner_self]
  have hre : (inner ℂ (J p) (R u)).re = (inner ℂ (R u) (J p)).re := by
    simpa using inner_re_symm (𝕜 := ℂ) (J p) (R u)
  simp only [RCLike.re_to_complex, Complex.add_re, hre, Complex.mul_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im] at *
  nlinarith [h0]

lemma g68m_comp {D : Submodule ℂ H} (gp g : NoiseGauge N) (S : StandardData (N := N) D) :
    gaugeAction gp (gaugeAction g S) = gaugeAction (gaugeMul gp g) S := by
  apply g68m_sd_ext
  · apply LinearMap.ext; intro psi
    rw [g68m_GL, g68m_GL, g68m_GL, map_add, g68m_rot_ins, ← ContinuousLinearMap.comp_apply,
      g68m_rot_mul]
    simp only [gaugeMul]
    rw [g68m_ins_add]; abel
  · apply LinearMap.ext; intro psi
    rw [g68m_GK, g68m_GK, g68m_GK, g68m_GL]
    apply ext_inner_right ℂ; intro h
    have hRR : ∀ x, noiseRotation gp (noiseRotation g x) = noiseRotation (H := H) (gaugeMul gp g) x := by
      intro x; rw [← ContinuousLinearMap.comp_apply, g68m_rot_mul]
    have ha : (gaugeMul gp g).a = gp.Dnoise g.a + gp.a := rfl
    have hb : (gaugeMul gp g).b = g.b + gp.b - (inner ℂ gp.a (gp.Dnoise g.a)).im := rfl
    rw [ha, hb]
    simp only [inner_add_left, inner_smul_left, ContinuousLinearMap.adjoint_inner_left, map_add]
    rw [hRR, g68m_rot_ins, g68m_inner_ins, g68m_ins_add, inner_add_right, ← g68m_rot_ins gp g.a h,
      ← hRR, g68m_rot_inner, g68m_conj_c, g68m_conj_c, g68m_conj_c]
    set z := inner ℂ gp.a (gp.Dnoise g.a)
    have hz : inner ℂ (gp.Dnoise g.a) gp.a = (starRingEnd ℂ) z := (inner_conj_symm _ _).symm
    have hnorm : ‖gp.Dnoise g.a + gp.a‖ ^ 2 = ‖g.a‖ ^ 2 + 2 * z.re + ‖gp.a‖ ^ 2 := by
      rw [@norm_add_sq ℂ, LinearIsometryEquiv.norm_map, hz]
      simp
    rw [hz, hnorm]
    have key : ((((‖g.a‖ ^ 2 + 2 * z.re + ‖gp.a‖ ^ 2) / 2 : ℝ) : ℂ) +
        Complex.I * (((g.b + gp.b - z.im : ℝ)) : ℂ)) =
        (((‖g.a‖ ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (g.b : ℂ)) +
        (((‖gp.a‖ ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (gp.b : ℂ)) + (starRingEnd ℂ) z := by
      apply Complex.ext <;> simp <;> ring
    rw [key]
    ring

lemma g68m_idact {D : Submodule ℂ H} (S : StandardData (N := N) D) :
    gaugeAction gaugeIdentity S = S := by
  have hJ : noiseInsertion (H := H) (gaugeIdentity (N := N)).a = 0 := by
    ext h; exact g68m_ins_zero h
  apply g68m_sd_ext
  · apply LinearMap.ext; intro psi
    rw [g68m_GL, g68m_rot_id, hJ]; simp
  · apply LinearMap.ext; intro psi
    rw [g68m_GK, hJ]; simp [gaugeIdentity]

lemma g68m_assoc (gpp gp g : NoiseGauge N) :
    gaugeMul gpp (gaugeMul gp g) = gaugeMul (gaugeMul gpp gp) g := by
  apply g68m_gauge_ext
  · exact LinearIsometryEquiv.ext fun x => rfl
  · simp only [gaugeMul, LinearIsometryEquiv.trans_apply, map_add]; abel
  · simp only [gaugeMul, LinearIsometryEquiv.trans_apply, map_add, inner_add_left,
      inner_add_right, Complex.add_im, LinearIsometryEquiv.inner_map_map]
    ring

lemma g68m_laws (g : NoiseGauge N) :
    gaugeMul gaugeIdentity g = g ∧ gaugeMul g gaugeIdentity = g ∧
      gaugeMul (noiseGaugeInverse g) g = gaugeIdentity ∧
      gaugeMul g (noiseGaugeInverse g) = gaugeIdentity := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply g68m_gauge_ext
    · exact LinearIsometryEquiv.ext fun x => rfl
    · simp [gaugeMul, gaugeIdentity]
    · simp [gaugeMul, gaugeIdentity]
  · apply g68m_gauge_ext
    · exact LinearIsometryEquiv.ext fun x => rfl
    · simp [gaugeMul, gaugeIdentity]
    · simp [gaugeMul, gaugeIdentity]
  · apply g68m_gauge_ext
    · exact LinearIsometryEquiv.ext fun x => by simp [gaugeMul, gaugeIdentity, noiseGaugeInverse]
    · simp [gaugeMul, gaugeIdentity, noiseGaugeInverse]
    · simp [gaugeMul, gaugeIdentity, noiseGaugeInverse]
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
  · apply g68m_gauge_ext
    · exact LinearIsometryEquiv.ext fun x => by simp [gaugeMul, gaugeIdentity, noiseGaugeInverse]
    · simp [gaugeMul, gaugeIdentity, noiseGaugeInverse]
    · simp [gaugeMul, gaugeIdentity, noiseGaugeInverse]
      rw [← Complex.ofReal_pow, Complex.ofReal_im]

theorem solution {D : Submodule ℂ H}
    (hDense : Dense (D : Set H)) (S : StandardData (N := N) D)
    (hDiss : IsDissipative S) :
    (∀ g : NoiseGauge N,
      (∀ (psi : D) (X : H →L[ℂ] H) (phi : D),
        standardForm (gaugeAction g S) psi X phi = standardForm S psi X phi) ∧
      IsDissipative (gaugeAction g S)) ∧
    (∀ gp g : NoiseGauge N,
      gaugeAction gp (gaugeAction g S) = gaugeAction (gaugeMul gp g) S) ∧
    (gaugeAction gaugeIdentity S = S) ∧
    (∀ gpp gp g : NoiseGauge N,
      gaugeMul gpp (gaugeMul gp g) = gaugeMul (gaugeMul gpp gp) g) ∧
    (∀ g : NoiseGauge N,
      gaugeMul gaugeIdentity g = g ∧ gaugeMul g gaugeIdentity = g ∧
      gaugeMul (noiseGaugeInverse g) g = gaugeIdentity ∧
      gaugeMul g (noiseGaugeInverse g) = gaugeIdentity) := by
  refine ⟨fun g => ⟨fun psi X phi => g68m_form g S psi X phi, g68m_diss g S hDiss⟩,
    fun gp g => g68m_comp gp g S, g68m_idact S, g68m_assoc, g68m_laws⟩

end
