-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.choi_kraus_minimality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:05:34.777537+00:00
-- url     : https://prove2.me/submissions/17820997-5da9-4ea7-a43b-f327371d66d5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

open Matrix
theorem x8_spec {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (h : M.IsHermitian)
    (x y : n) : M x y = ∑ k, (h.eigenvalues k : ℂ) * (h.eigenvectorBasis k) x *
      star ((h.eigenvectorBasis k) y) := by
  conv_lhs => rw [h.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, mul_apply, diagonal_apply, IsHermitian.eigenvectorUnitary_apply,
    star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem x8_kentry (F : K → Matrix B A ℂ) (rho : Matrix A A ℂ) (b b' : B) :
    krausApply F rho b b' = ∑ a, ∑ a', rho a a' * ∑ j, F j b a * star (F j b' a') := by
  have : ∀ j, (F j * rho * (F j)ᴴ) b b' = ∑ a, ∑ a', F j b a * rho a a' * star (F j b' a') := by
    intro j
    simp only [mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  simp only [krausApply, Matrix.sum_apply, this, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem x8_choi (F : K → Matrix B A ℂ) (x y : A × B) :
    normalizedChoi (krausApply F) x y =
      (∑ j, F j x.2 x.1 * star (F j y.2 y.1)) / (Fintype.card A : ℂ) := by
  simp only [normalizedChoi, x8_kentry]
  congr 1
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem x8_gram [Nonempty A] (F : K → Matrix B A ℂ) :
    normalizedChoi (krausApply F) =
      (Matrix.of fun j (x : A × B) => star (F j x.2 x.1) /
        (Real.sqrt (Fintype.card A : ℝ) : ℂ))ᴴ *
      (Matrix.of fun j (x : A × B) => star (F j x.2 x.1) /
        (Real.sqrt (Fintype.card A : ℝ) : ℂ)) := by
  ext x y
  rw [x8_choi, mul_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : (Real.sqrt (Fintype.card A : ℝ) : ℂ) * (Real.sqrt (Fintype.card A : ℝ) : ℂ) =
      (Fintype.card A : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have hs0 : (Real.sqrt (Fintype.card A : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by exact_mod_cast Fintype.card_pos))
  simp only [conjTranspose_apply, of_apply, star_div₀, star_star, Complex.star_def,
    Complex.conj_ofReal]
  rw [← hs]
  field_simp
  rw [Complex.conj_conj]; ring

theorem x8_same {L' : Type*} [Fintype L'] (F : K → Matrix B A ℂ) (G : L' → Matrix B A ℂ)
    (h : ∀ a c b b', ∑ j, F j b a * star (F j b' c) = ∑ l, G l b a * star (G l b' c)) :
    krausApply F = krausApply G ∧ ∑ j, (F j)ᴴ * F j = ∑ l, (G l)ᴴ * G l := by
  refine ⟨?_, ?_⟩
  · funext rho; ext b b'
    simp only [x8_kentry, h]
  · ext a c
    simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := L'))]
    refine Finset.sum_congr rfl fun b _ => ?_
    have := h c a b b
    calc ∑ j, star (F j b a) * F j b c = ∑ j, F j b c * star (F j b a) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = ∑ l, G l b c * star (G l b a) := this
      _ = _ := Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem x8_main [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) :
    (normalizedChoi Phi).IsHermitian ∧
    Matrix.rank (normalizedChoi Phi) = krausNumber Phi ∧
    Fintype.card (ChoiSupport Phi) = krausNumber Phi ∧
    IsKrausFamily (spectralKraus Phi) ∧ krausApply (spectralKraus Phi) = Phi ∧
    krausNumber Phi ≤ Fintype.card A * Fintype.card B ∧
    ∃ F : Fin (krausNumber Phi) → Matrix B A ℂ, IsKrausFamily F ∧ Phi = krausApply F := by
  obtain ⟨m, E, hE, hPE⟩ := hPhi
  have hPhiE : Phi = krausApply E := funext hPE
  have hJ := x8_gram E
  rw [← hPhiE] at hJ
  have hPSD : (normalizedChoi Phi).PosSemidef := by rw [hJ]; exact posSemidef_conjTranspose_mul_self _
  have hH : (normalizedChoi Phi).IsHermitian := hPSD.isHermitian
  have hev : ∀ k, choiEigenvalue Phi k = hH.eigenvalues k := fun k => by
    rw [choiEigenvalue, dif_pos hH]
  have hevec : ∀ k, choiEigenvector Phi k = hH.eigenvectorBasis k := fun k => by
    rw [choiEigenvector, dif_pos hH]
  have hnn : ∀ k, 0 ≤ hH.eigenvalues k := fun k => hPSD.eigenvalues_nonneg k
  have hd0 : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  -- the spectral family reproduces the Kraus "Choi" sums
  have hspec : ∀ a c b b', ∑ j, E j b a * star (E j b' c) =
      ∑ k, spectralKraus Phi k b a * star (spectralKraus Phi k b' c) := by
    intro a c b b'
    have h1 : ∑ j, E j b a * star (E j b' c) =
        (Fintype.card A : ℂ) * normalizedChoi Phi (a, b) (c, b') := by
      rw [hPhiE, x8_choi]; field_simp
    rw [h1, x8_spec hH, Finset.mul_sum]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k => choiEigenvalue Phi k ≠ 0)]
    have h2 : ∑ k : {k // ¬ choiEigenvalue Phi k ≠ 0}, (Fintype.card A : ℂ) *
        ((hH.eigenvalues k : ℂ) * (hH.eigenvectorBasis k) (a, b) *
          star ((hH.eigenvectorBasis k) (c, b'))) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have := k.2; rw [not_not, hev] at this; simp [this]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [spectralKraus, hev, hevec, star_mul', Complex.star_def, Complex.conj_ofReal]
    have h3 : (Real.sqrt ((Fintype.card A : ℝ) * hH.eigenvalues k.val) : ℂ) *
        (Real.sqrt ((Fintype.card A : ℝ) * hH.eigenvalues k.val) : ℂ) =
        (Fintype.card A : ℂ) * (hH.eigenvalues k.val : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (mul_nonneg (Nat.cast_nonneg _) (hnn _))]
      simp
    linear_combination ((hH.eigenvectorBasis k.val) (a, b) *
      (starRingEnd ℂ) ((hH.eigenvectorBasis k.val) (c, b'))) * h3.symm
  obtain ⟨hSa, hSg⟩ := x8_same E (spectralKraus Phi) hspec
  have hSK : IsKrausFamily (spectralKraus Phi) := by
    unfold IsKrausFamily; rw [← hSg]; exact hE
  have hSA : krausApply (spectralKraus Phi) = Phi := by rw [← hSa, hPhiE]
  -- rank bound for any Kraus family
  have hrank_le : ∀ r (F : Fin r → Matrix B A ℂ), Phi = krausApply F →
      (normalizedChoi Phi).rank ≤ r := by
    intro r F hF
    rw [hF, x8_gram, rank_conjTranspose_mul_self]
    simpa using rank_le_card_height (Matrix.of fun j (x : A × B) => star (F j x.2 x.1) /
        (Real.sqrt (Fintype.card A : ℝ) : ℂ))
  have hrankS : (normalizedChoi Phi).rank = Fintype.card (ChoiSupport Phi) := by
    rw [hH.rank_eq_card_non_zero_eigs]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun k => by rw [hev])
  -- the spectral family reindexed by Fin
  set n := Fintype.card (ChoiSupport Phi)
  let eS := Fintype.equivFin (ChoiSupport Phi)
  let G : Fin n → Matrix B A ℂ := fun i => spectralKraus Phi (eS.symm i)
  have hG : ∀ a c b b', ∑ k, spectralKraus Phi k b a * star (spectralKraus Phi k b' c) =
      ∑ i, G i b a * star (G i b' c) := by
    intro a c b b'
    exact (Equiv.sum_comp eS.symm (fun k => spectralKraus Phi k b a *
      star (spectralKraus Phi k b' c))).symm
  obtain ⟨hGa, hGg⟩ := x8_same (spectralKraus Phi) G hG
  have hmem : n ∈ {r | ∃ F : Fin r → Matrix B A ℂ, IsKrausFamily F ∧ Phi = krausApply F} :=
    ⟨G, by unfold IsKrausFamily; rw [← hGg]; exact hSK, by rw [← hGa, hSA]⟩
  have hle : krausNumber Phi ≤ n := Nat.sInf_le hmem
  obtain ⟨F0, hF0, hPF0⟩ := Nat.sInf_mem ⟨n, hmem⟩
  have hge : (normalizedChoi Phi).rank ≤ krausNumber Phi := hrank_le _ F0 hPF0
  have hkn : krausNumber Phi = n := le_antisymm hle (hrankS ▸ hge)
  refine ⟨hH, by rw [hrankS, hkn], hkn.symm, hSK, hSA, ?_, F0, hF0, hPF0⟩
  rw [hkn, ← hrankS, ← Fintype.card_prod]
  exact rank_le_card_height _

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 QAlgorithms.Papers.Independent.Claimed50.P48
  QAlgorithms.Papers.Independent.Information100.P56 in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) :
    (normalizedChoi Phi).IsHermitian ∧
    Matrix.rank (normalizedChoi Phi) = krausNumber Phi ∧
    Fintype.card (ChoiSupport Phi) = krausNumber Phi ∧
    IsKrausFamily (spectralKraus Phi) ∧ krausApply (spectralKraus Phi) = Phi ∧
    krausNumber Phi ≤ Fintype.card A * Fintype.card B ∧
    ∃ F : Fin (krausNumber Phi) → Matrix B A ℂ, IsKrausFamily F ∧ Phi = krausApply F :=
  x8_main Phi hPhi
