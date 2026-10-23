-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P06.channel_test_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:59:20.495944+00:00
-- url     : https://prove2.me/submissions/ce02c102-c3eb-4788-94a2-9aa59722fded

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace X7W2CT

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P06
open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)

theorem X7_choi_apply {I O : Type} (M : QMap I O) (a b : I) (o o' : O) :
    choi M (a, o) (b, o') = M (Matrix.single a b 1) o o' := rfl

theorem X7_lin_expand {I O : Type} [Fintype I] (M : QMap I O)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem X7_sum_psd {I ι : Type} [Fintype I] (s : Finset ι) (A : ι → Matrix I I ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem X7_swap22 {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := by
  calc ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ i, ∑ m, ∑ j, ∑ l, f i j m l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ l, f i j m l := Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ l, ∑ j, f i j m l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem X7_cp_of_choi {I O : Type} [Fintype I] [Fintype O]
    (M : QMap I O) (hC : (choi M).PosSemidef) :
    Entanglement.IsCompletelyPositive M := by
  intro r X hX
  obtain ⟨m1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  obtain ⟨m2, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hMij : ∀ i j o o', M (Matrix.single i j 1) o o' =
      ∑ l, g l (i, o) * star (g l (j, o')) := by
    intro i j o o'
    rw [← X7_choi_apply, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  let F : Fin m1 → Fin m2 → (Fin r × O → ℂ) :=
    fun a l q => ∑ i, v a (q.1, i) * g l (i, q.2)
  have hY : idTensorSuperop M X = ∑ a, ∑ l, Matrix.vecMulVec (F a l) (star (F a l)) := by
    ext ⟨x, o⟩ ⟨y, o'⟩
    show M (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
    rw [X7_lin_expand]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, hv,
      Matrix.vecMulVec_apply, Pi.star_apply, F, star_sum, star_mul']
    simp only [Finset.sum_mul_sum]
    rw [X7_swap22]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hY]
  exact X7_sum_psd _ _ fun a => X7_sum_psd _ _ fun l =>
    Matrix.posSemidef_vecMulVec_self_star _

theorem X7_choi_of_cp {I O : Type} [Fintype I] [Fintype O]
    (M : QMap I O) (h : Entanglement.IsCompletelyPositive M) :
    (choi M).PosSemidef := by
  let e := Fintype.equivFin I
  let Ω : Fin (Fintype.card I) × I → ℂ := fun q => if q.1 = e q.2 then 1 else 0
  have hY := h _ _ (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hE : choi M = (idTensorSuperop M (Matrix.vecMulVec Ω (star Ω))).submatrix
      (fun q : I × O => (e q.1, q.2)) (fun q => (e q.1, q.2)) := by
    ext ⟨i, o⟩ ⟨i', o'⟩
    rw [X7_choi_apply, Matrix.submatrix_apply]
    show M (Matrix.single i i' 1) o o' =
      M (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) o o'
    have hX : (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) =
        Matrix.single i i' 1 := by
      ext j j'
      by_cases h1 : i = j <;> by_cases h2 : i' = j' <;>
        simp [Matrix.single_apply, Matrix.vecMulVec_apply, Ω, h1, h2, Ne.symm, eq_comm]
    rw [hX]
  rw [hE]
  exact hY.submatrix _

theorem X7_choi_lfc {I O : Type} [Fintype I] {d : DecidableEq I} (J : Op (I × O)) :
    @choi I O d (linearFromChoi J) = J := by
  ext ⟨a, o⟩ ⟨b, o'⟩
  show (∑ x, ∑ y, Matrix.single a b (1 : ℂ) x y * J (x, o) (y, o')) = _
  simp [Matrix.single_apply, ite_and]

theorem X7_choi_lfc_apply {I O : Type} [Fintype I] {d : DecidableEq I} (J : Op (I × O))
    (x y : I × O) : @choi I O d (linearFromChoi J) x y = J x y := by
  rw [X7_choi_lfc]

theorem X7_lfc_add {I O : Type} [Fintype I] (J K : Op (I × O)) :
    linearFromChoi (J + K) = linearFromChoi J + linearFromChoi K := by
  apply LinearMap.ext; intro X; ext i j
  show (∑ a, ∑ b, X a b * (J + K) (a, i) (b, j)) =
    (∑ a, ∑ b, X a b * J (a, i) (b, j)) + (∑ a, ∑ b, X a b * K (a, i) (b, j))
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem X7_choi_add {I O : Type} (E F : QMap I O) :
    choi (E + F) = choi E + choi F := by
  ext p q; rfl

/-- positivity from CP -/
theorem X7_pos_of_cp {I O : Type} [Fintype I] [Fintype O]
    (M : QMap I O) (h : Entanglement.IsCompletelyPositive M) (X : Op I)
    (hX : X.PosSemidef) : (M X).PosSemidef := by
  have hX' : (X.submatrix (fun p : Fin 1 × I => p.2) (fun p => p.2)).PosSemidef :=
    hX.submatrix _
  have := (h 1 _ hX').submatrix (fun o : O => ((0 : Fin 1), o))
  convert this using 1
  ext o o'
  rfl

/-- CPP gives: S (choi E) PSD for CP E. -/
theorem X7_super_cp {A0 A1 B0 B1 : Type} [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1]
    (S : Supermap A0 A1 B0 B1) (hS : IsCPP S) (E : QMap A0 A1)
    (hE : Entanglement.IsCompletelyPositive E) :
    Entanglement.IsCompletelyPositive (superApply S E) := by
  let J1 : Op ((Fin 1 × A0) × (Fin 1 × A1)) :=
    (choi E).submatrix (fun p => (p.1.2, p.2.2)) (fun p => (p.1.2, p.2.2))
  have hJ1 : J1.PosSemidef := (X7_choi_of_cp E hE).submatrix _
  have hN := hS 1 1 one_pos one_pos (linearFromChoi J1)
    (X7_cp_of_choi _ (by rw [X7_choi_lfc]; exact hJ1))
  have hC := X7_choi_of_cp _ hN
  apply X7_cp_of_choi
  unfold superApply
  rw [X7_choi_lfc]
  have hC2 := hC.submatrix (fun q : B0 × B1 => (((0 : Fin 1), q.1), ((0 : Fin 1), q.2)))
  unfold superExtend at hC2
  simp only [X7_choi_lfc_apply] at hC2
  convert hC2 using 1
  ext p q
  rw [Matrix.submatrix_apply]
  erw [X7_choi_lfc_apply]
  rfl

theorem X7_perm3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ l, f a b l = ∑ l, ∑ b, ∑ a, f a b l := by
  calc ∑ a, ∑ b, ∑ l, f a b l = ∑ a, ∑ l, ∑ b, f a b l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, f a b l := Finset.sum_comm
    _ = ∑ l, ∑ b, ∑ a, f a b l := Finset.sum_congr rfl fun l _ => Finset.sum_comm

/-- Kraus representation from a PSD Choi matrix. -/
theorem X7_kraus_of_choi {I O : Type} [Fintype I] [Fintype O]
    (M : QMap I O) (h : (choi M).PosSemidef) :
    ∃ m : ℕ, ∃ K : Fin m → Matrix O I ℂ, ∀ X, M X = krausApply K X := by
  obtain ⟨m, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp h
  have hMij : ∀ i j o o', M (Matrix.single i j 1) o o' =
      ∑ l, g l (i, o) * star (g l (j, o')) := by
    intro i j o o'
    rw [← X7_choi_apply, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  refine ⟨m, fun l => Matrix.of fun o i => g l (i, o), fun X => ?_⟩
  ext o o'
  rw [X7_lin_expand]
  simp only [krausApply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hMij,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [X7_perm3]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => ?_
  ring

theorem X7_choi_kraus_psd {I O : Type} [Fintype I] [Fintype O] {m : ℕ}
    (M : QMap I O) (K : Fin m → Matrix O I ℂ) (hM : ∀ X, M X = krausApply K X) :
    (choi M).PosSemidef := by
  have : choi M = ∑ l, Matrix.vecMulVec (fun p : I × O => K l p.2 p.1)
      (star (fun p : I × O => K l p.2 p.1)) := by
    ext ⟨a, o⟩ ⟨b, o'⟩
    rw [X7_choi_apply, hM]
    simp [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, ite_and, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [this]
  exact X7_sum_psd _ _ fun l => Matrix.posSemidef_vecMulVec_self_star _

theorem X7_kraus_trace {I O : Type} [Fintype I] [Fintype O] {m : ℕ}
    (K : Fin m → Matrix O I ℂ) (X : Op I) :
    (krausApply K X).trace = ((∑ l, (K l)ᴴ * K l) * X).trace := by
  simp only [krausApply, Matrix.trace_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]

theorem X7_trace_vmv {I : Type} [Fintype I] (P : Op I) (x : I → ℂ) :
    (P * Matrix.vecMulVec x (star x)).trace = star x ⬝ᵥ (P *ᵥ x) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem X7_one_sub_psd {I : Type} [Fintype I] (P : Op I) (hP : P.PosSemidef)
    (hT : ∀ X : Op I, IsDensityMatrix X → ((P * X).trace).re ≤ 1) :
    (1 - P).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_one.sub hP.1) fun x => ?_
  have hPx := hP.dotProduct_mulVec_nonneg x
  have hxx : 0 ≤ star x ⬝ᵥ x := by
    have := (Matrix.PosSemidef.one (n := I) (R := ℂ)).dotProduct_mulVec_nonneg x
    simpa using this
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
  rw [Complex.nonneg_iff] at hPx hxx ⊢
  refine ⟨?_, by simp [← hPx.2, ← hxx.2]⟩
  rw [Complex.sub_re, sub_nonneg]
  by_cases h0 : (star x ⬝ᵥ x).re = 0
  · -- then x = 0
    have hx : x = 0 := by
      have : star x ⬝ᵥ x = 0 := Complex.ext h0 (by simpa using hxx.2.symm)
      exact dotProduct_star_self_eq_zero.mp this
    subst hx; simp
  · have hpos : 0 < (star x ⬝ᵥ x).re := lt_of_le_of_ne hxx.1 (Ne.symm h0)
    set t := (star x ⬝ᵥ x).re
    have htc : star x ⬝ᵥ x = (t : ℂ) := Complex.ext rfl (by simpa using hxx.2.symm)
    let ρ : Op I := ((t⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec x (star x)
    have hρ : IsDensityMatrix ρ := by
      constructor
      · refine Matrix.PosSemidef.smul (Matrix.posSemidef_vecMulVec_self_star x) ?_
        exact_mod_cast (inv_nonneg.mpr hxx.1)
      · have h1 : (Matrix.vecMulVec x (star x)).trace = star x ⬝ᵥ x := by
          simpa using X7_trace_vmv 1 x
        simp only [ρ, Matrix.trace_smul, h1, htc, smul_eq_mul]
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hpos), Complex.ofReal_one]
    have := hT ρ hρ
    simp only [ρ, Matrix.mul_smul, Matrix.trace_smul, X7_trace_vmv, smul_eq_mul,
      Complex.re_ofReal_mul] at this
    have := mul_le_mul_of_nonneg_left this (le_of_lt hpos)
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul, mul_one] at this
    exact this

/-- Kraus map as a linear map. -/
def X7_krausLin {I O : Type} [Fintype I] {m : ℕ} (K : Fin m → Matrix O I ℂ) : QMap I O where
  toFun := krausApply K
  map_add' X Y := by
    simp [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem X7_chan_cptni {I O : Type} [Fintype I] [Fintype O]
    (N : QMap I O) (hN : IsChannel N) : IsCPTNI N := by
  obtain ⟨m, K, hK, hNK⟩ := hN
  refine ⟨X7_cp_of_choi _ (X7_choi_kraus_psd N K hNK), fun X hX => ?_⟩
  rw [hNK, X7_kraus_trace]
  unfold IsKrausFamily at hK
  rw [hK, Matrix.one_mul, hX.2]
  simp

end X7W2CT

namespace X7W2CT

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P06
open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)

theorem X7_superApply_add {A0 A1 B0 B1 : Type} [Fintype A0] [Fintype B0]
    (S : Supermap A0 A1 B0 B1) (E F : QMap A0 A1) :
    superApply S (E + F) = superApply S E + superApply S F := by
  unfold superApply
  rw [X7_choi_add, map_add, X7_lfc_add]

theorem X7_backward {A0 A1 B0 B1 : Type} [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [Nonempty A0] [hA1 : Nonempty A1] [Nonempty B0] [Nonempty B1]
    (S : Supermap A0 A1 B0 B1) (hS : IsCPP S)
    (hN : ∀ N : QMap A0 A1, IsChannel N → IsCPTNI (superApply S N))
    (E : QMap A0 A1) (hE : IsCPTNI E) : IsCPTNI (superApply S E) := by
  obtain ⟨hEcp, hEt⟩ := hE
  refine ⟨X7_super_cp S hS E hEcp, fun ρ hρ => ?_⟩
  obtain ⟨m1, K, hK⟩ := X7_kraus_of_choi E (X7_choi_of_cp E hEcp)
  set P : Op A0 := ∑ l, (K l)ᴴ * K l with hPdef
  have hPpsd : P.PosSemidef :=
    X7_sum_psd _ _ fun l => Matrix.posSemidef_conjTranspose_mul_self _
  have hD : (1 - P).PosSemidef := by
    refine X7_one_sub_psd P hPpsd fun X hX => ?_
    have := hEt X hX
    rwa [hK, X7_kraus_trace] at this
  obtain ⟨m2, h, hh⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hD
  have a1 : A1 := Classical.arbitrary A1
  let G : Fin m2 → Matrix A1 A0 ℂ := fun k => Matrix.of fun o i =>
    if o = a1 then star (h k i) else 0
  have hG : ∑ k, (G k)ᴴ * G k = 1 - P := by
    rw [hh]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext i j
    simp [G, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply]
  let F : QMap A0 A1 := X7_krausLin G
  have hFcp : Entanglement.IsCompletelyPositive F :=
    X7_cp_of_choi _ (X7_choi_kraus_psd F G fun _ => rfl)
  have hChan : IsChannel (E + F) := by
    refine ⟨m1 + m2, Fin.append K G, ?_, fun X => ?_⟩
    · unfold IsKrausFamily
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hG, ← hPdef]
      abel
    · show E X + F X = _
      rw [hK]
      show krausApply K X + krausApply G X = _
      simp only [krausApply]
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  have h1 := (hN _ hChan).2 ρ hρ
  rw [X7_superApply_add, LinearMap.add_apply, Matrix.trace_add, Complex.add_re] at h1
  have h2 : 0 ≤ ((superApply S F) ρ).trace.re := by
    have := (X7_pos_of_cp _ (X7_super_cp S hS F hFcp) ρ hρ.1).trace_nonneg
    exact (Complex.nonneg_iff.mp this).1
  linarith

end X7W2CT

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P06 X7W2CT in
theorem solution {A0 A1 B0 B1 : Type} [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [hA0 : Nonempty A0] [hA1 : Nonempty A1] [hB0 : Nonempty B0] [hB1 : Nonempty B1]
    (S : Supermap A0 A1 B0 B1) (hS : IsCPP S) :
    (∀ E : QMap A0 A1, IsCPTNI E → IsCPTNI (superApply S E)) ↔
      (∀ N : QMap A0 A1, IsChannel N → IsCPTNI (superApply S N)) := by
  constructor
  · intro h N hN
    exact h N (X7_chan_cptni N hN)
  · intro h E hE
    exact X7_backward S hS h E hE

end
