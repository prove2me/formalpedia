-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P29.typicalRestriction_reliability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:27:26.747168+00:00
-- url     : https://prove2.me/submissions/5249221a-9c1d-46f0-844e-bc3b008556c2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7P29_lin_expand {I J : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (X : Matrix I I ℂ) :
    L X = ∑ i, ∑ j, X i j • L (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem X7P29_choi_psd {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (h : Entanglement.IsCompletelyPositive L) :
    (Matrix.of fun (p q : I × J) => L (Matrix.single p.1 q.1 1) p.2 q.2).PosSemidef := by
  let e := Fintype.equivFin I
  let Ω : Fin (Fintype.card I) × I → ℂ := fun q => if q.1 = e q.2 then 1 else 0
  have hY := h _ _ (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hE : (Matrix.of fun (p q : I × J) => L (Matrix.single p.1 q.1 1) p.2 q.2) =
      (idTensorSuperop L (Matrix.vecMulVec Ω (star Ω))).submatrix
      (fun q : I × J => (e q.1, q.2)) (fun q => (e q.1, q.2)) := by
    ext ⟨i, o⟩ ⟨i', o'⟩
    rw [Matrix.submatrix_apply, Matrix.of_apply]
    show L (Matrix.single i i' 1) o o' =
      L (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) o o'
    have hX : (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) =
        Matrix.single i i' 1 := by
      ext j j'
      by_cases h1 : i = j <;> by_cases h2 : i' = j' <;>
        simp [Matrix.single_apply, Matrix.vecMulVec_apply, Ω, h1, h2, Ne.symm, eq_comm]
    rw [hX]
  rw [hE]
  exact hY.submatrix _

theorem X7P29_perm3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ l, f a b l = ∑ l, ∑ b, ∑ a, f a b l := by
  calc ∑ a, ∑ b, ∑ l, f a b l = ∑ a, ∑ l, ∑ b, f a b l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, f a b l := Finset.sum_comm
    _ = ∑ l, ∑ b, ∑ a, f a b l := Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem X7P29_kraus {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (h : Entanglement.IsCompletelyPositive L) :
    ∃ m : ℕ, ∃ K : Fin m → Matrix J I ℂ, ∀ X, L X = krausApply K X := by
  obtain ⟨m, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (X7P29_choi_psd L h)
  have hMij : ∀ i j o o', L (Matrix.single i j 1) o o' =
      ∑ l, g l (i, o) * star (g l (j, o')) := by
    intro i j o o'
    have := congrFun (congrFun hg (i, o)) (j, o')
    rw [Matrix.of_apply] at this
    rw [this, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  refine ⟨m, fun l => Matrix.of fun o i => g l (i, o), fun X => ?_⟩
  ext o o'
  rw [X7P29_lin_expand]
  simp only [krausApply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hMij,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [X7P29_perm3]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => ?_
  ring

theorem X7P29_entry {I : Type*} [Fintype I] [DecidableEq I] (K : Matrix I I ℂ) (i j k l : I) :
    (K * (Matrix.single j l (1:ℂ) : Matrix I I ℂ) * Kᴴ) i k = K i j * conj (K k l) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

theorem X7P29_fe {I : Type*} [Fintype I] [DecidableEq I] {κ : Type*} [Fintype κ]
    (rho : Matrix I I ℂ) (A : Superop I I) (K : κ → Matrix I I ℂ)
    (hA : ∀ X, A X = krausApply K X) :
    fe rho A = ∑ a, Complex.normSq ((K a * rho).trace) := by
  unfold fe
  have h5 : ∀ f : I → I → I → I → κ → ℂ, ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, f i j k l a =
      ∑ a, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l a := by
    intro f
    calc _ = ∑ i, ∑ j, ∑ k, ∑ a, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ a, ∑ k, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ k, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have ht : ∀ a, (K a * rho).trace = ∑ i, ∑ j, K a i j * rho j i := by
    intro a; simp [Matrix.trace, Matrix.mul_apply]
  have key : (∑ i, ∑ j, ∑ k, ∑ l, rho j i * conj (rho l k) * A (Matrix.single j l (1:ℂ)) i k) =
      ∑ a, (K a * rho).trace * conj ((K a * rho).trace) := by
    simp only [hA, krausApply, Matrix.sum_apply, X7P29_entry, Finset.mul_sum]
    rw [h5]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ht, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul]
    ring
  rw [key, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re]

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7T_proj {ι : Type*} [Fintype ι] [DecidableEq ι] (rho : Matrix ι ι ℂ)
    (hrho : rho.IsHermitian) (f : ℝ → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    let P := cfc f rho
    P * P = P ∧ Pᴴ = P ∧ P * rho = rho * P := by
  intro P
  have hsa : IsSelfAdjoint rho := hrho
  have hcont : ContinuousOn f (spectrum ℝ rho) := Matrix.finite_real_spectrum.continuousOn f
  refine ⟨?_, ?_, ?_⟩
  · show cfc f rho * cfc f rho = cfc f rho
    rw [← cfc_mul f f rho]
    congr 1
    funext x
    rcases hf x with h | h <;> simp [h]
  · exact (cfc_predicate f rho : IsSelfAdjoint (cfc f rho))
  · show cfc f rho * rho = rho * cfc f rho
    exact (Commute.refl rho).cfc_real f |>.symm.eq.symm

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7T_tr_mul_ct {I L : Type*} [Fintype I] [Fintype L] (X Y : Matrix I L ℂ) :
    (X * Yᴴ).trace = ∑ i, ∑ l, X i l * star (Y i l) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Complex Cauchy–Schwarz on a finite double sum. -/
theorem X7T_cs_sum {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    Complex.normSq (∑ k, a k * star (b k)) ≤
      (∑ k, Complex.normSq (a k)) * (∑ k, Complex.normSq (b k)) := by
  have h1 : ‖∑ k, a k * star (b k)‖ ≤ ∑ k, ‖a k‖ * ‖b k‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_mul, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖a k‖) (fun k => ‖b k‖)
  rw [Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ k, a k * star (b k)‖ ^ 2 ≤ (∑ k, ‖a k‖ * ‖b k‖) ^ 2 := by
        gcongr
    _ ≤ _ := h2

theorem X7T_cs {I : Type*} [Fintype I] (E sigma : Matrix I I ℂ) (hs : sigma.PosSemidef) :
    Complex.normSq (E * sigma).trace ≤ sigma.trace.re * (Eᴴ * E * sigma).trace.re := by
  obtain ⟨n, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hs
  let G : Matrix I (Fin n) ℂ := Matrix.of fun i l => g l i
  have hG : sigma = G * Gᴴ := by
    rw [hg]; ext i i'
    simp [G, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Matrix.conjTranspose_apply]
  have e1 : (E * sigma).trace = ∑ i, ∑ l, (E * G) i l * star (G i l) := by
    rw [hG, ← Matrix.mul_assoc, X7T_tr_mul_ct]
  have e2 : sigma.trace = ((∑ i, ∑ l, Complex.normSq (G i l) : ℝ) : ℂ) := by
    rw [hG, X7T_tr_mul_ct]; push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  have e3 : (Eᴴ * E * sigma).trace = ((∑ i, ∑ l, Complex.normSq ((E * G) i l) : ℝ) : ℂ) := by
    have : (Eᴴ * E * sigma).trace = ((E * G) * (E * G)ᴴ).trace := by
      rw [hG, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [this, X7T_tr_mul_ct]; push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  rw [e1, e2, e3, Complex.ofReal_re, Complex.ofReal_re, mul_comm]
  have := X7T_cs_sum (fun p : I × Fin n => (E * G) p.1 p.2) (fun p => G p.1 p.2)
  simpa only [Fintype.sum_prod_type] using this

theorem X7T_fe_le {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ} (EK : Fin m → Matrix I I ℂ)
    (hK : ∑ a, (EK a)ᴴ * EK a = 1) (sigma : Matrix I I ℂ) (hs : sigma.PosSemidef) :
    ∑ a, Complex.normSq (EK a * sigma).trace ≤ sigma.trace.re ^ 2 := by
  calc ∑ a, Complex.normSq (EK a * sigma).trace
      ≤ ∑ a, sigma.trace.re * ((EK a)ᴴ * EK a * sigma).trace.re :=
        Finset.sum_le_sum fun a _ => X7T_cs _ _ hs
    _ = sigma.trace.re * ((∑ a, (EK a)ᴴ * EK a) * sigma).trace.re := by
        rw [← Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    _ = _ := by rw [hK, Matrix.one_mul, sq]

theorem X7T_alg {m : ℕ} (u v : Fin m → ℂ) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hu : ∑ a, Complex.normSq (u a) ≤ μ ^ 2) (hv : ∑ a, Complex.normSq (v a) ≤ (1 - μ) ^ 2) :
    |∑ a, Complex.normSq (u a) / μ ^ 2 - ∑ a, Complex.normSq (u a + v a)| ≤ 4 * (1 - μ) := by
  set U := ∑ a, Complex.normSq (u a)
  set V := ∑ a, Complex.normSq (v a)
  set X := ∑ a, (u a * star (v a)).re
  have hsum : ∑ a, Complex.normSq (u a + v a) = U + V + 2 * X := by
    simp only [U, V, X, Complex.normSq_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      Complex.star_def]
  have hX : |X| ≤ Real.sqrt U * Real.sqrt V := by
    have h1 : |X| ≤ ‖∑ a, u a * star (v a)‖ := by
      simp only [X, ← Complex.re_sum]
      exact Complex.abs_re_le_norm _
    have h2 := X7T_cs_sum u v
    rw [Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖∑ a, u a * star (v a)‖ ≤ Real.sqrt (U * V) :=
      Real.le_sqrt_of_sq_le h2
    rw [Real.sqrt_mul (Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _)] at h3
    linarith
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  have hsU : Real.sqrt U ≤ μ := Real.sqrt_le_iff.mpr ⟨hμ0.le, hu⟩
  have hsV : Real.sqrt V ≤ 1 - μ := Real.sqrt_le_iff.mpr ⟨by linarith, hv⟩
  have hXb : |X| ≤ μ * (1 - μ) :=
    hX.trans (mul_le_mul hsU hsV (Real.sqrt_nonneg _) hμ0.le)
  rw [hsum, ← Finset.sum_div]
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hq : U / μ ^ 2 ≤ 1 := (div_le_one hμ2).mpr hu
  have hq0 : 0 ≤ U / μ ^ 2 := div_nonneg hU0 hμ2.le
  have hUeq : U = μ ^ 2 * (U / μ ^ 2) := by field_simp
  rw [abs_le]
  rcases abs_le.mp hXb with ⟨hX1, hX2⟩
  set q := U / μ ^ 2
  have hA : 0 ≤ q * (1 - μ ^ 2) := mul_nonneg hq0 (by nlinarith)
  have hB : q * (1 - μ ^ 2) ≤ 1 - μ ^ 2 := by
    have : 0 ≤ 1 - μ ^ 2 := by nlinarith
    nlinarith
  have hD : q - (U + V + 2 * X) = q * (1 - μ ^ 2) - V - 2 * X := by rw [hUeq]; ring
  rw [hD]
  constructor <;> nlinarith [hX1, hX2, hA, hB, hv, hV0, hμ1, hμ0]

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7T_main (S : BlockQuantumSource) (window : ℝ) (n : ℕ)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1)
    (hmass : 1 - delta ≤ qaepRetainedMass S window n)
    (E : Superop (SourceRegister S.dimension n) (SourceRegister S.dimension n)) (hE : IsChannel E) :
    |fe (typicalRestriction S window n) E - fe (S.rho n) E| ≤
      4 * delta / (1 - delta) ^ 2 := by
  have hρ := S.density n
  have hP : qaepSpectralProjector S window n * qaepSpectralProjector S window n =
        qaepSpectralProjector S window n ∧
      (qaepSpectralProjector S window n)ᴴ = qaepSpectralProjector S window n ∧
      qaepSpectralProjector S window n * S.rho n = S.rho n * qaepSpectralProjector S window n := by
    unfold qaepSpectralProjector
    exact X7T_proj (S.rho n) hρ.1.1 _ (fun x => by split_ifs <;> simp)
  set P := qaepSpectralProjector S window n with hPdef
  set ρ := S.rho n with hρdef
  obtain ⟨hPP, hPh, hPc⟩ := hP
  set α := P * ρ * P with hα
  set β := (1 - P) * ρ * (1 - P) with hβ
  have hαβ : α + β = ρ := by
    have h1 : α = ρ * P := by rw [hα, hPc, Matrix.mul_assoc, hPP]
    have h2 : β = ρ - ρ * P := by
      rw [hβ, Matrix.sub_mul, Matrix.one_mul, hPc, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
        Matrix.mul_assoc, hPP]
      abel
    rw [h1, h2]; abel
  have hαpsd : α.PosSemidef := by
    have := hρ.1.mul_mul_conjTranspose_same P
    rwa [hPh] at this
  have hβpsd : β.PosSemidef := by
    have := hρ.1.mul_mul_conjTranspose_same (1 - P)
    rwa [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh] at this
  set μ := qaepRetainedMass S window n with hμ
  have hμα : μ = α.trace.re := rfl
  have htr : α.trace.re + β.trace.re = 1 := by
    rw [← Complex.add_re, ← Matrix.trace_add, hαβ, hρ.2, Complex.one_re]
  have hβ0 : 0 ≤ β.trace.re := (Complex.nonneg_iff.mp hβpsd.trace_nonneg).1
  have hμ1 : μ ≤ 1 := by linarith
  have hμ0 : 0 < μ := by linarith
  obtain ⟨m, EK, hK, hEK⟩ := hE
  let u : Fin m → ℂ := fun a => (EK a * α).trace
  let v : Fin m → ℂ := fun a => (EK a * β).trace
  have hfe1 : fe ρ E = ∑ a, Complex.normSq (u a + v a) := by
    rw [X7P29_fe ρ E EK hEK]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [u, v]
    rw [← Matrix.trace_add, ← Matrix.mul_add, hαβ]
  have hfe2 : fe (typicalRestriction S window n) E = ∑ a, Complex.normSq (u a) / μ ^ 2 := by
    rw [X7P29_fe _ E EK hEK]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : typicalRestriction S window n = ((μ : ℂ)⁻¹) • α := rfl
    rw [this, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.normSq_mul,
      Complex.normSq_inv, Complex.normSq_ofReal]
    simp only [u]
    field_simp
  have hu : ∑ a, Complex.normSq (u a) ≤ μ ^ 2 := by
    rw [hμα]; exact X7T_fe_le EK hK α hαpsd
  have hv : ∑ a, Complex.normSq (v a) ≤ (1 - μ) ^ 2 := by
    have : 1 - μ = β.trace.re := by rw [hμα]; linarith
    rw [this]; exact X7T_fe_le EK hK β hβpsd
  rw [hfe1, hfe2]
  refine (X7T_alg u v μ hμ0 hμ1 hu hv).trans ?_
  have h1 : 4 * (1 - μ) ≤ 4 * delta := by linarith
  refine h1.trans ?_
  have hd : 0 < (1 - delta) ^ 2 := by have : 0 < 1 - delta := by linarith
                                      positivity
  rw [le_div_iff₀ hd]
  have : (1 - delta) ^ 2 ≤ 1 := by nlinarith
  nlinarith

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7R2_main (S : BlockQuantumSource) (hS : QAEP S)
    (window : ℝ) (hwindow : 0 < window)
    (A : (n : ℕ) → Superop (SourceRegister S.dimension n) (SourceRegister S.dimension n))
    (hA : ∀ n, IsChannel (A n)) :
    (Tendsto (fun n => fe (S.rho n) (A n)) atTop (nhds 1) ↔
      Tendsto (fun n => fe (typicalRestriction S window n) (A n)) atTop (nhds 1)) := by
  set d : ℕ → ℝ := fun n => fe (typicalRestriction S window n) (A n) - fe (S.rho n) (A n) with hd
  have hd0 : Tendsto d atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set δ : ℝ := min (1 / 2) (ε / 32) with hδ
    have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
    have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
    have hδ2 : δ ≤ ε / 32 := min_le_right _ _
    filter_upwards [hS window hwindow δ hδ0] with n hn
    have h := X7T_main S window n δ hδ0.le (by linarith) hn.le (A n) (hA n)
    rw [Real.dist_eq, sub_zero]
    refine lt_of_le_of_lt h ?_
    have hq : (1 / 2 : ℝ) ^ 2 ≤ (1 - δ) ^ 2 := by nlinarith
    rw [div_lt_iff₀ (by nlinarith)]
    nlinarith
  constructor
  · intro h
    have := h.add hd0
    simp only [add_zero] at this
    refine this.congr fun n => ?_
    simp [hd]
  · intro h
    have := h.sub hd0
    simp only [sub_zero] at this
    refine this.congr fun n => ?_
    simp [hd]

end QAlgorithms.Papers.Independent.Gap48.P29

end

open QAlgorithms Filter QAlgorithms.Papers.Independent.Gap48.P29 in
theorem solution (S : BlockQuantumSource) (hS : QAEP S)
    (window : ℝ) (hwindow : 0 < window)
    (A : (n : ℕ) → Superop (SourceRegister S.dimension n) (SourceRegister S.dimension n))
    (hA : ∀ n, IsChannel (A n)) :
    (Tendsto (fun n => fe (S.rho n) (A n)) atTop (nhds 1) ↔
      Tendsto (fun n => fe (typicalRestriction S window n) (A n)) atTop (nhds 1)) :=
  QAlgorithms.Papers.Independent.Gap48.P29.X7R2_main S hS window hwindow A hA
