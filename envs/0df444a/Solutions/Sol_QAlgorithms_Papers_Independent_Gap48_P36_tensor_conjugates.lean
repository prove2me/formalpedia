-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.tensor_conjugates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:23:22.030296+00:00
-- url     : https://prove2.me/submissions/7f9d435d-581f-4a38-9157-3c3b7cf3540c

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

section gen
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- coefficient of a vector on an eigenvector. -/
def x8c {J : Matrix X X ℂ} (hH : J.IsHermitian) (k : X) (f : X → ℂ) : ℂ :=
  ∑ x, star ((hH.eigenvectorBasis k) x) * f x

theorem x8_orth {J : Matrix X X ℂ} (hH : J.IsHermitian) (k k' : X) :
    ∑ x, star ((hH.eigenvectorBasis k) x) * (hH.eigenvectorBasis k') x =
      if k = k' then 1 else 0 := by
  have := (hH.eigenvectorBasis).orthonormal
  rw [orthonormal_iff_ite] at this
  have h := this k k'
  rw [PiLp.inner_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mul_comm]

theorem x8_compl {J : Matrix X X ℂ} (hH : J.IsHermitian) (x y : X) :
    ∑ k, (hH.eigenvectorBasis k) x * star ((hH.eigenvectorBasis k) y) =
      if x = y then 1 else 0 := by
  have hU := hH.eigenvectorUnitary.2
  rw [Matrix.mem_unitaryGroup_iff] at hU
  have := congrFun (congrFun hU x) y
  simp only [mul_apply, star_apply, IsHermitian.eigenvectorUnitary_apply, one_apply] at this
  exact this

theorem x8_expand {J : Matrix X X ℂ} (hH : J.IsHermitian) (f : X → ℂ) (x : X) :
    ∑ k, x8c hH k f * (hH.eigenvectorBasis k) x = f x := by
  simp only [x8c, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ y, ∑ k, star ((hH.eigenvectorBasis k) y) * f y * (hH.eigenvectorBasis k) x =
      f y * if x = y then 1 else 0 := by
    intro y; rw [← x8_compl hH x y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  simp only [this]
  simp

theorem x8_eig {J : Matrix X X ℂ} (hH : J.IsHermitian) (k : X) (x : X) :
    ∑ y, J x y * (hH.eigenvectorBasis k) y = (hH.eigenvalues k : ℂ) * (hH.eigenvectorBasis k) x := by
  simp only [x8_spec hH, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ k', ∑ y, (hH.eigenvalues k' : ℂ) * (hH.eigenvectorBasis k') x *
      star ((hH.eigenvectorBasis k') y) * (hH.eigenvectorBasis k) y =
      (hH.eigenvalues k' : ℂ) * (hH.eigenvectorBasis k') x * (if k' = k then 1 else 0) := by
    intro k'; rw [← x8_orth hH k' k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_; ring
  simp only [this]
  simp

variable {J : Matrix X X ℂ} (hH : J.IsHermitian) {c : ℝ} {K' : Type*} [Fintype K']

theorem x8_K1 (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (k x : X) : ∑ j, f j x * star (x8c hH k (f j)) =
      c * (hH.eigenvalues k : ℂ) * (hH.eigenvectorBasis k) x := by
  simp only [x8c, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ y, ∑ j, f j x * ((hH.eigenvectorBasis k) y * star (f j y)) =
      (c : ℂ) * (J x y * (hH.eigenvectorBasis k) y) := by
    intro y
    rw [← mul_assoc, ← hf, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_; ring
  simp only [this, ← Finset.mul_sum, x8_eig]
  ring

theorem x8_K2 (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (k k' : X) : ∑ j, star (x8c hH k (f j)) * x8c hH k' (f j) =
      if k' = k then c * (hH.eigenvalues k : ℂ) else 0 := by
  have : ∀ j, star (x8c hH k (f j)) * x8c hH k' (f j) =
      ∑ x, star ((hH.eigenvectorBasis k') x) * (f j x * star (x8c hH k (f j))) := by
    intro j
    rw [show x8c hH k' (f j) = ∑ x, star ((hH.eigenvectorBasis k') x) * f j x from rfl,
      Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_; ring
  simp only [this]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, x8_K1 hH f hf]
  have h2 : ∀ x, star ((hH.eigenvectorBasis k') x) *
      (c * (hH.eigenvalues k : ℂ) * (hH.eigenvectorBasis k) x) =
      c * (hH.eigenvalues k : ℂ) * (star ((hH.eigenvectorBasis k') x) * (hH.eigenvectorBasis k) x) :=
    fun x => by ring
  simp only [h2, ← Finset.mul_sum, x8_orth]
  split_ifs <;> simp

theorem x8_K3 (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (k : X) (hk : hH.eigenvalues k = 0) (j : K') : x8c hH k (f j) = 0 := by
  have h := x8_K2 hH f hf k k
  simp only [if_true, hk, Complex.ofReal_zero, mul_zero] at h
  have h' : ∑ j, Complex.normSq (x8c hH k (f j)) = 0 := by
    have : ((∑ j, Complex.normSq (x8c hH k (f j)) : ℝ) : ℂ) = 0 := by
      rw [← h, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    exact_mod_cast this
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)] at h'
  exact Complex.normSq_eq_zero.mp (h' j (Finset.mem_univ _))

def x8s (c : ℝ) (k : X) : ℂ := (Real.sqrt (c * hH.eigenvalues k) : ℂ)

def x8α (c : ℝ) (f : K' → X → ℂ) : Matrix K' {k // hH.eigenvalues k ≠ 0} ℂ :=
  Matrix.of fun j k => x8c hH k.1 (f j) / x8s hH c k.1

variable (hc : 0 < c) (hnn : ∀ k, 0 ≤ hH.eigenvalues k)
include hc hnn

theorem x8_ss (k : X) (hk : hH.eigenvalues k ≠ 0) :
    x8s hH c k * x8s hH c k = c * (hH.eigenvalues k : ℂ) ∧ x8s hH c k ≠ 0 ∧
      star (x8s hH c k) = x8s hH c k := by
  have hpos : 0 < c * hH.eigenvalues k := mul_pos hc (lt_of_le_of_ne (hnn k) (Ne.symm hk))
  refine ⟨?_, ?_, ?_⟩
  · rw [x8s, ← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]; simp
  · rw [x8s]; exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hpos)
  · rw [x8s, Complex.star_def, Complex.conj_ofReal]

theorem x8_αgram (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y) :
    (x8α hH c f)ᴴ * x8α hH c f = 1 := by
  ext k k'
  obtain ⟨h1, h2, h3⟩ := x8_ss hH hc hnn k.1 k.2
  obtain ⟨h1', h2', h3'⟩ := x8_ss hH hc hnn k'.1 k'.2
  simp only [mul_apply, conjTranspose_apply, x8α, of_apply, star_div₀, h3]
  have : ∀ j, star (x8c hH k.1 (f j)) / x8s hH c k.1 * (x8c hH k'.1 (f j) / x8s hH c k'.1) =
      (star (x8c hH k.1 (f j)) * x8c hH k'.1 (f j)) / (x8s hH c k.1 * x8s hH c k'.1) := by
    intro j; field_simp
  simp only [this, ← Finset.sum_div, x8_K2 hH f hf, one_apply]
  by_cases hkk : k = k'
  · subst hkk; simp only [if_true, h1]; exact div_self (h1 ▸ mul_ne_zero h2 h2)
  · have : ¬ k'.1 = k.1 := fun h => hkk (Subtype.ext h).symm
    simp [hkk, this]

theorem x8_K4 (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (k : {k // hH.eigenvalues k ≠ 0}) (x : X) :
    ∑ j, star (x8α hH c f j k) * f j x = x8s hH c k.1 * (hH.eigenvectorBasis k.1) x := by
  obtain ⟨h1, h2, h3⟩ := x8_ss hH hc hnn k.1 k.2
  simp only [x8α, of_apply, star_div₀, h3]
  have : ∀ j, star (x8c hH k.1 (f j)) / x8s hH c k.1 * f j x =
      (f j x * star (x8c hH k.1 (f j))) / x8s hH c k.1 := fun j => by ring
  simp only [this, ← Finset.sum_div, x8_K1 hH f hf, ← h1]
  field_simp

theorem x8_K5 (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (j : K') (x : X) :
    ∑ k : {k // hH.eigenvalues k ≠ 0}, x8α hH c f j k * (x8s hH c k.1 * (hH.eigenvectorBasis k.1) x)
      = f j x := by
  have : ∀ k : {k // hH.eigenvalues k ≠ 0}, x8α hH c f j k * (x8s hH c k.1 * (hH.eigenvectorBasis k.1) x)
      = x8c hH k.1 (f j) * (hH.eigenvectorBasis k.1) x := by
    intro k
    obtain ⟨h1, h2, h3⟩ := x8_ss hH hc hnn k.1 k.2
    simp only [x8α, of_apply]; field_simp
  simp only [this]
  rw [← x8_expand hH (f j) x, ← Fintype.sum_subtype_add_sum_subtype (fun k => hH.eigenvalues k ≠ 0)]
  have h0 : ∑ k : {k // ¬ hH.eigenvalues k ≠ 0}, x8c hH k.1 (f j) * (hH.eigenvectorBasis k.1) x = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [x8_K3 hH f hf k.1 (not_not.mp k.2) j, zero_mul]
  rw [h0, add_zero]

theorem x8_W {L' : Type*} [Fintype L'] (f : K' → X → ℂ) (g : L' → X → ℂ)
    (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (hg : ∀ x y, ∑ l, g l x * star (g l y) = c * J x y) :
    let W := x8α hH c f * (x8α hH c g)ᴴ
    (∀ j x, ∑ l, W j l * g l x = f j x) ∧ (∀ l x, ∑ j, star (W j l) * f j x = g l x) ∧
    W * Wᴴ * W = W ∧ W.rank = Fintype.card {k // hH.eigenvalues k ≠ 0} := by
  intro W
  have hαf := x8_αgram hH hc hnn f hf
  have hαg := x8_αgram hH hc hnn g hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j x
    simp only [W, mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, x8_K4 hH hc hnn g hg]
    exact x8_K5 hH hc hnn f hf j x
  · intro l x
    simp only [W, mul_apply, conjTranspose_apply, star_sum, star_mul', star_star, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ k : {k // hH.eigenvalues k ≠ 0}, ∑ j, star (x8α hH c f j k) * x8α hH c g l k * f j x =
        x8α hH c g l k * (x8s hH c k.1 * (hH.eigenvectorBasis k.1) x) := by
      intro k; rw [← x8_K4 hH hc hnn f hf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_; ring
    simp only [this]
    exact x8_K5 hH hc hnn g hg l x
  · simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x8α hH c g)ᴴ, hαg, Matrix.one_mul, ← Matrix.mul_assoc (x8α hH c f)ᴴ, hαf,
      Matrix.one_mul]
  · apply le_antisymm
    · calc W.rank ≤ (x8α hH c f).rank := rank_mul_le_left _ _
        _ = ((x8α hH c f)ᴴ * x8α hH c f).rank := (rank_conjTranspose_mul_self _).symm
        _ = _ := by rw [hαf, rank_one]
    · have : x8α hH c f = W * x8α hH c g := by
        simp only [W, Matrix.mul_assoc, hαg, Matrix.mul_one]
      calc Fintype.card {k // hH.eigenvalues k ≠ 0} = (1 : Matrix {k // hH.eigenvalues k ≠ 0}
            {k // hH.eigenvalues k ≠ 0} ℂ).rank := (rank_one).symm
        _ = ((x8α hH c f)ᴴ * x8α hH c f).rank := by rw [hαf]
        _ = (x8α hH c f).rank := rank_conjTranspose_mul_self _
        _ ≤ W.rank := by rw [this]; exact rank_mul_le_left _ _

end gen


theorem x8_chan {L' : Type*} [Fintype L'] (G : L' → Matrix B A ℂ) (hG : IsKrausFamily G) :
    IsChannel (krausApply G) := by
  let e := Fintype.equivFin L'
  have h := x8_same G (fun i => G (e.symm i)) (fun a c b b' =>
    (Equiv.sum_comp e.symm (fun k => G k b a * star (G k b' c))).symm)
  refine ⟨Fintype.card L', fun i => G (e.symm i), ?_, fun rho => by rw [h.1]⟩
  unfold IsKrausFamily; rw [← h.2]; exact hG

theorem x8_csum {L' : Type*} [Fintype L'] (F : K → Matrix B A ℂ) (G : L' → Matrix B A ℂ)
    (h : krausApply F = krausApply G) (a c : A) (b b' : B) :
    ∑ j, F j b a * star (F j b' c) = ∑ l, G l b a * star (G l b' c) := by
  have := congrFun (congrFun (congrArg normalizedChoi h) (a, b)) (c, b')
  rw [x8_choi, x8_choi] at this
  have hd : (Fintype.card A : ℂ) ≠ 0 := by
    have : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨a⟩
    exact_mod_cast this.ne'
  exact (div_left_inj' hd).mp this

theorem x8_main2 [Nonempty A] [Nonempty B] [Nonempty K] [Nonempty L]
    (F : K → Matrix B A ℂ) (G : L → Matrix B A ℂ)
    (hF : IsKrausFamily F) (hG : IsKrausFamily G) :
    (krausNumber (krausApply G) = Fintype.card L →
      ∀ U : Matrix K L ℂ, Uᴴ * U = 1 →
        IsKrausFamily (fun j => ∑ k, U j k • G k) ∧
        krausApply (fun j => ∑ k, U j k • G k) = krausApply G) ∧
    (krausApply F = krausApply G ↔ ∃ W : Matrix K L ℂ,
      PartialIsometry W ∧ Matrix.rank W = krausNumber (krausApply G) ∧
      (∀ j, F j = ∑ k, W j k • G k) ∧ (∀ k, G k = ∑ j, conj (W j k) • F j))
 := by
  refine ⟨?_, ?_⟩
  · intro _ U hU
    have hUe : ∀ k' k, ∑ j, star (U j k') * U j k = if k' = k then 1 else 0 := by
      intro k' k
      have := congrFun (congrFun hU k') k
      simpa [mul_apply, one_apply] using this
    have h : ∀ a c b b', ∑ j, (∑ k, U j k • G k) b a * star ((∑ k, U j k • G k) b' c) =
        ∑ l, G l b a * star (G l b' c) := by
      intro a c b b'
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, star_sum, star_mul',
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      have : ∀ i, ∑ j, U j i * G i b a * (star (U j k) * star (G k b' c)) =
          (∑ j, star (U j k) * U j i) * (G i b a * star (G k b' c)) := by
        intro i; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      simp only [this, hUe]
      simp
    obtain ⟨h1, h2⟩ := x8_same _ G h
    refine ⟨?_, h1⟩
    unfold IsKrausFamily; rw [h2]; exact hG
  constructor
  · intro hFG
    set J := normalizedChoi (krausApply G) with hJdef
    have hJ := x8_gram G
    have hPSD : J.PosSemidef := by rw [hJdef, hJ]; exact posSemidef_conjTranspose_mul_self _
    have hH : J.IsHermitian := hPSD.isHermitian
    have hnn : ∀ k, 0 ≤ hH.eigenvalues k := fun k => hPSD.eigenvalues_nonneg k
    have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
    have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hg : ∀ x y : A × B, ∑ l, G l x.2 x.1 * star (G l y.2 y.1) =
        ((Fintype.card A : ℝ) : ℂ) * J x y := by
      intro x y; rw [hJdef, x8_choi]; push_cast; field_simp
    have hf : ∀ x y : A × B, ∑ j, F j x.2 x.1 * star (F j y.2 y.1) =
        ((Fintype.card A : ℝ) : ℂ) * J x y := by
      intro x y; rw [x8_csum F G hFG, hg]
    obtain ⟨W1, W2, W3, W4⟩ := x8_W hH hc hnn (fun j (x : A × B) => F j x.2 x.1)
      (fun l (x : A × B) => G l x.2 x.1) hf hg
    obtain ⟨-, -, hcard, -⟩ := x8_main (krausApply G) (x8_chan G hG)
    refine ⟨_, W3, ?_, ?_, ?_⟩
    · rw [W4, ← hcard]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun k => by
        rw [choiEigenvalue, dif_pos hH])
    · intro j; ext b a
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      exact (W1 j (a, b)).symm
    · intro l; ext b a
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      exact (W2 l (a, b)).symm
  · rintro ⟨W, -, -, e1, e2⟩
    have e1' : ∀ j b a, F j b a = ∑ l, W j l * G l b a := fun j b a => by
      rw [e1 j]; simp [Matrix.sum_apply]
    have e2' : ∀ l b a, G l b a = ∑ j, star (W j l) * F j b a := fun l b a => by
      rw [e2 l]; simp [Matrix.sum_apply]
    refine (x8_same F G fun a c b b' => ?_).1
    calc ∑ j, F j b a * star (F j b' c) = ∑ j, ∑ l, W j l * G l b a * star (F j b' c) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          conv_lhs => rw [e1' j b a]
          rw [Finset.sum_mul]
      _ = ∑ l, G l b a * ∑ j, W j l * star (F j b' c) := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ = ∑ l, G l b a * star (G l b' c) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [e2' l b' c, star_sum]
          simp [star_mul']

end QAlgorithms.Papers.Independent.Gap48.P36


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

theorem x8_recv (V : Matrix (B × C) A ℂ) (rho : Matrix A A ℂ) (b b' : B) :
    receiverChannel V rho b b' = ∑ a, ∑ a', rho a a' * ∑ c, V (b, c) a * star (V (b', c) a') := by
  simp only [receiverChannel, QAlgorithms.traceRight, of_apply, mul_apply, conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext y; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun c _ => ?_
  ring

theorem x8_comp (V : Matrix (B × C) A ℂ) (rho : Matrix A A ℂ) (c c' : C) :
    complementaryChannel V rho c c' = ∑ a, ∑ a', rho a a' * ∑ b, V (b, c) a * star (V (b, c') a') := by
  simp only [complementaryChannel, traceLeft, of_apply, mul_apply, conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext y; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun b _ => ?_
  ring

theorem x8_recvK (V : Matrix (B × C) A ℂ) :
    receiverChannel V = krausApply (fun c => Matrix.of fun b a => V (b, c) a) := by
  funext rho; ext b b'
  rw [x8_recv, x8_kentry]; simp

theorem x8_compK (V : Matrix (B × C) A ℂ) :
    complementaryChannel V = krausApply (fun b => Matrix.of fun c a => V (b, c) a) := by
  funext rho; ext c c'
  rw [x8_comp, x8_kentry]; simp

theorem x8_main3 [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (Phi : Superop A B) (Psi : Superop A C) (Xi : Superop A D)
    (hPhi : IsChannel Phi) (hPsi : CPComplementary Phi Psi) (hXi : CPComplementary Phi Xi) :
    ∃ W : Matrix C D ℂ, PartialIsometry W ∧ Matrix.rank W = krausNumber Phi ∧
      (∀ rho, Psi rho = W * Xi rho * Wᴴ) ∧ (∀ rho, Xi rho = Wᴴ * Psi rho * W) := by
  obtain ⟨V, hV1, hV2⟩ := hPsi
  obtain ⟨V', hV1', hV2'⟩ := hXi
  rw [x8_recvK] at hV1 hV1'
  set f := fun c (x : A × B) => V (x.2, c) x.1
  set g := fun d (x : A × B) => V' (x.2, d) x.1
  set J := normalizedChoi Phi with hJdef
  have hJ := x8_gram (fun c => Matrix.of fun b a => V (b, c) a)
  rw [hV1] at hJ
  have hPSD : J.PosSemidef := by rw [hJdef, hJ]; exact posSemidef_conjTranspose_mul_self _
  have hH : J.IsHermitian := hPSD.isHermitian
  have hnn : ∀ k, 0 ≤ hH.eigenvalues k := fun k => hPSD.eigenvalues_nonneg k
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hf : ∀ x y : A × B, ∑ c, f c x * star (f c y) = ((Fintype.card A : ℝ) : ℂ) * J x y := by
    intro x y; rw [hJdef, ← hV1, x8_choi]; push_cast; field_simp; simp [f]
  have hg : ∀ x y : A × B, ∑ d, g d x * star (g d y) = ((Fintype.card A : ℝ) : ℂ) * J x y := by
    intro x y; rw [hJdef, ← hV1', x8_choi]; push_cast; field_simp; simp [g]
  obtain ⟨W1, W2, W3, W4⟩ := x8_W hH hc hnn f g hf hg
  obtain ⟨-, -, hcard, -⟩ := x8_main Phi hPhi
  set W := x8α hH (Fintype.card A : ℝ) f * (x8α hH (Fintype.card A : ℝ) g)ᴴ
  clear_value W
  have hR : ∀ b, (Matrix.of fun c a => V (b, c) a) = W * Matrix.of fun d a => V' (b, d) a := by
    intro b; ext c a; rw [mul_apply]; exact (W1 c (a, b)).symm
  have hR' : ∀ b, (Matrix.of fun d a => V' (b, d) a) = Wᴴ * Matrix.of fun c a => V (b, c) a := by
    intro b; ext d a; rw [mul_apply]; exact (W2 d (a, b)).symm
  refine ⟨W, W3, ?_, ?_, ?_⟩
  · rw [W4, ← hcard]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun k => by rw [choiEigenvalue, dif_pos hH])
  · intro rho
    rw [← hV2, ← hV2', x8_compK, x8_compK]
    simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hR b]; simp only [conjTranspose_mul, Matrix.mul_assoc]
  · intro rho
    rw [← hV2, ← hV2', x8_compK, x8_compK]
    simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hR' b]; simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

end QAlgorithms.Papers.Independent.Gap48.P36


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

theorem x8_ksingle {K' : Type*} [Fintype K'] (E : K' → Matrix B A ℂ) (a c : A) (b b' : B) :
    krausApply E (Matrix.single a c 1) b b' = ∑ i, E i b a * star (E i b' c) := by
  rw [x8_kentry]; simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem x8_tensorK {K' L' : Type*} [Fintype K'] [Fintype L'] (E : K' → Matrix B A ℂ)
    (E' : L' → Matrix B2 A2 ℂ) :
    superopTensor (krausApply E) (krausApply E') =
      krausApply (fun p : K' × L' => E p.1 ⊗ₖ E' p.2) := by
  funext X; ext ⟨b, b2⟩ ⟨b', b2'⟩
  rw [x8_kentry]
  simp only [superopTensor, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, kroneckerMap_apply,
    x8_ksingle, Fintype.sum_prod_type, star_mul']
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a2 _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c2 _ => ?_
  congr 1
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem x8_tensorKF {K' L' : Type*} [Fintype K'] [Fintype L'] (E : K' → Matrix B A ℂ)
    (E' : L' → Matrix B2 A2 ℂ) (hE : IsKrausFamily E) (hE' : IsKrausFamily E') :
    IsKrausFamily (fun p : K' × L' => E p.1 ⊗ₖ E' p.2) := by
  unfold IsKrausFamily at *
  simp only [conjTranspose_kronecker, ← mul_kronecker_mul, Fintype.sum_prod_type]
  have key : ∀ (X : K' → Matrix A A ℂ) (Y : L' → Matrix A2 A2 ℂ),
      ∑ i, ∑ j, X i ⊗ₖ Y j = (∑ i, X i) ⊗ₖ (∑ j, Y j) := by
    intro X Y; ext ⟨a, a2⟩ ⟨c, c2⟩
    simp [Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul_sum]
  rw [key, hE, hE', one_kronecker_one]

theorem x8_main4 [Nonempty A] [Nonempty B] [Nonempty C]
    [Nonempty A2] [Nonempty B2] [Nonempty C2] [Nonempty D]
    (Phi : Superop A B) (Psi : Superop A2 B2)
    (PhiC : Superop A C) (PsiC : Superop A2 C2)
    (hPhi : IsChannel Phi) (hPsi : IsChannel Psi)
    (hc : CPComplementary Phi PhiC) (hd : CPComplementary Psi PsiC) :
    CPComplementary (superopTensor Phi Psi) (superopTensor PhiC PsiC) ∧
    ∀ Xi : Superop (A × A2) D, CPComplementary (superopTensor Phi Psi) Xi →
      ∃ W : Matrix D (C × C2) ℂ, PartialIsometry W ∧
        ∀ rho, Xi rho = W * superopTensor PhiC PsiC rho * Wᴴ := by
  obtain ⟨V, hV1, hV2⟩ := hc
  obtain ⟨V', hV1', hV2'⟩ := hd
  have h1 : CPComplementary (superopTensor Phi Psi) (superopTensor PhiC PsiC) := by
    refine ⟨tensorDilation V V', ?_, ?_⟩
    · rw [← hV1, ← hV1', x8_recvK, x8_recvK, x8_recvK, x8_tensorK]
      congr 1
    · rw [← hV2, ← hV2', x8_compK, x8_compK, x8_compK, x8_tensorK]
      congr 1
  have hch : IsChannel (superopTensor Phi Psi) := by
    obtain ⟨m, E, hE, hPE⟩ := hPhi
    obtain ⟨m', E', hE', hPE'⟩ := hPsi
    have : superopTensor Phi Psi = krausApply (fun p : Fin m × Fin m' => E p.1 ⊗ₖ E' p.2) := by
      rw [← x8_tensorK, show Phi = krausApply E from funext hPE, show Psi = krausApply E' from funext hPE']
    rw [this]; exact x8_chan _ (x8_tensorKF E E' hE hE')
  refine ⟨h1, fun Xi hXi => ?_⟩
  obtain ⟨W, hW, -, -, h2⟩ := x8_main3 _ _ Xi hch h1 hXi
  refine ⟨Wᴴ, ?_, fun rho => by rw [h2 rho, conjTranspose_conjTranspose]⟩
  unfold PartialIsometry at *
  conv_rhs => rw [← hW]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix ComplexConjugate in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 QAlgorithms.Papers.Independent.Claimed50.P48
  QAlgorithms.Papers.Independent.Information100.P56 in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution {A B C D A2 B2 C2 : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] [Fintype A2] [DecidableEq A2]
    [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2] [Nonempty A] [Nonempty B] [Nonempty C]
    [Nonempty A2] [Nonempty B2] [Nonempty C2] [Nonempty D]
    (Phi : Superop A B) (Psi : Superop A2 B2)
    (PhiC : Superop A C) (PsiC : Superop A2 C2)
    (hPhi : IsChannel Phi) (hPsi : IsChannel Psi)
    (hc : CPComplementary Phi PhiC) (hd : CPComplementary Psi PsiC) :
    CPComplementary (superopTensor Phi Psi) (superopTensor PhiC PsiC) ∧
    ∀ Xi : Superop (A × A2) D, CPComplementary (superopTensor Phi Psi) Xi →
      ∃ W : Matrix D (C × C2) ℂ, PartialIsometry W ∧
        ∀ rho, Xi rho = W * superopTensor PhiC PsiC rho * Wᴴ :=
  x8_main4 Phi Psi PhiC PsiC hPhi hPsi hc hd
