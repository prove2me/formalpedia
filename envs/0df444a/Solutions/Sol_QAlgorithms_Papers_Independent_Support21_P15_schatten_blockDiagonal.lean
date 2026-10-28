-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P15.schatten_blockDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:17:31.325341+00:00
-- url     : https://prove2.me/submissions/e84a2e03-2051-4d3e-8bc8-4a61b4dd96aa

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P15

noncomputable section

open scoped BigOperators

open Filter

open QAlgorithms.Papers.Independent.Support21.P15

namespace E36

open Matrix Polynomial
open scoped ComplexOrder
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def Tsum (φ : ℝ → ℝ) (q : ℂ[X]) : ℝ := (q.roots.map fun z => φ z.re).sum

lemma trace_cfc_re (M : Matrix I I ℂ) (hM : M.IsHermitian) (φ : ℝ → ℝ) :
    ((cfc φ M).trace).re = Tsum φ M.charpoly := by
  rw [Tsum, hM.roots_charpoly_eq_eigenvalues, hM.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp [Multiset.map_map, Function.comp_def, Matrix.trace_diagonal]

lemma trace_cfc_conj (W : Matrix I I ℂ) (hW : star W * W = 1) (d : I → ℝ) (φ : ℝ → ℝ) :
    (W * diagonal (fun s => (d s : ℂ)) * star W).IsHermitian ∧
    ((cfc φ (W * diagonal (fun s => (d s : ℂ)) * star W)).trace).re = ∑ s, φ (d s) := by
  have hH : (W * diagonal (fun s => (d s : ℂ)) * star W).IsHermitian := by
    unfold Matrix.IsHermitian
    simp [Matrix.mul_assoc, Matrix.conjTranspose_mul, star_eq_conjTranspose]
    have : star (fun s => (d s : ℂ)) = fun s => (d s : ℂ) := by
      funext s; simp
    rw [this]
  refine ⟨hH, ?_⟩
  rw [trace_cfc_re _ hH]
  have hcp : (W * diagonal (fun s => (d s : ℂ)) * star W).charpoly = ∏ s, (X - C (d s : ℂ)) := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hW, Matrix.one_mul]
    simp [Matrix.charpoly_diagonal]
  rw [hcp, Tsum]
  have : (∏ s, (X - C (d s : ℂ))) = ((Finset.univ.val.map (fun s => (d s : ℂ))).map (fun a => X - C a)).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]; rfl
  rw [this, Polynomial.roots_multiset_prod_X_sub_C]
  simp [Multiset.map_map, Function.comp_def]

lemma spectral' {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix I I ℂ) * diagonal (fun s => (hA.eigenvalues s : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix I I ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

lemma trace_cfc_eig {A : Matrix I I ℂ} (hA : A.IsHermitian) (φ : ℝ → ℝ) :
    ((cfc φ A).trace).re = ∑ s, φ (hA.eigenvalues s) := by
  have h := (trace_cfc_conj (hA.eigenvectorUnitary : Matrix I I ℂ)
    (by simp [Unitary.coe_star_mul_self]) hA.eigenvalues φ).2
  rw [← spectral' hA] at h
  exact h

variable {K L : Type*} [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]

def iota (x : K → Matrix L L ℂ) : Matrix (K × L) (K × L) ℂ :=
  fun i j => if i.1 = j.1 then x i.1 i.2 j.2 else 0

lemma iota_mul (x y : K → Matrix L L ℂ) : iota (fun k => x k * y k) = iota x * iota y := by
  ext ⟨k, a⟩ ⟨k', b⟩
  simp only [iota, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases h : k = k'
  · subst h
    simp [Matrix.mul_apply]
  · simp [h]

lemma iota_one : iota (fun _ : K => (1 : Matrix L L ℂ)) = 1 := by
  ext ⟨k, a⟩ ⟨k', b⟩
  simp only [iota, Matrix.one_apply, Prod.mk.injEq]
  by_cases h : k = k' <;> by_cases h' : a = b <;> simp [h, h']

lemma iota_star (x : K → Matrix L L ℂ) : iota (fun k => star (x k)) = star (iota x) := by
  ext ⟨k, a⟩ ⟨k', b⟩
  simp only [iota, Matrix.star_apply, Matrix.conjTranspose_apply]
  by_cases h : k = k'
  · subst h; simp
  · simp [h, Ne.symm h]

lemma iota_diag (d : K → L → ℂ) : iota (fun k => diagonal (d k)) = diagonal (fun p : K × L => d p.1 p.2) := by
  ext ⟨k, a⟩ ⟨k', b⟩
  simp only [iota, Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases h : k = k' <;> by_cases h' : a = b <;> simp [h, h']

lemma iota_spectral (y : K → Matrix L L ℂ) (hy : ∀ k, (y k).IsHermitian) :
    iota y = iota (fun k => ((hy k).eigenvectorUnitary : Matrix L L ℂ)) *
      diagonal (fun p : K × L => (((hy p.1).eigenvalues p.2 : ℝ) : ℂ)) *
      star (iota (fun k => ((hy k).eigenvectorUnitary : Matrix L L ℂ))) := by
  rw [← iota_star, ← iota_diag (fun k a => (((hy k).eigenvalues a : ℝ) : ℂ)), ← iota_mul, ← iota_mul]
  congr 1
  funext k
  exact spectral' (hy k)

lemma iota_unitary (y : K → Matrix L L ℂ) (hy : ∀ k, (y k).IsHermitian) :
    star (iota (fun k => ((hy k).eigenvectorUnitary : Matrix L L ℂ))) *
      iota (fun k => ((hy k).eigenvectorUnitary : Matrix L L ℂ)) = 1 := by
  rw [← iota_star, ← iota_mul, ← iota_one]
  congr 1
  funext k
  simp [Unitary.coe_star_mul_self]

lemma trace_cfc_iota (y : K → Matrix L L ℂ) (hy : ∀ k, (y k).IsHermitian) (φ : ℝ → ℝ) :
    ((iota y).IsHermitian) ∧ ((cfc φ (iota y)).trace).re = ∑ k, ((cfc φ (y k)).trace).re := by
  have h := trace_cfc_conj _ (iota_unitary y hy) (fun p : K × L => (hy p.1).eigenvalues p.2) φ
  rw [← iota_spectral y hy] at h
  refine ⟨h.1, h.2.trans ?_⟩
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [trace_cfc_eig (hy k)]


noncomputable def Nrm (p : ℝ) (A : Matrix I I ℂ) : ℝ :=
  ((cfc (fun t : ℝ => Real.rpow t (p / 2)) (Aᴴ * A)).trace).re

lemma Nrm_nonneg (p : ℝ) (A : Matrix I I ℂ) : 0 ≤ Nrm p A := by
  have hA : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  unfold Nrm
  rw [trace_cfc_eig hA]
  have hp := (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg
  exact Finset.sum_nonneg fun s _ => Real.rpow_nonneg (hp s) _

lemma Nrm_iota (p : ℝ) (x : K → Matrix L L ℂ) : Nrm p (iota x) = ∑ k, Nrm p (x k) := by
  unfold Nrm
  have h1 : (iota x)ᴴ * iota x = iota (fun k => (x k)ᴴ * x k) := by
    rw [show (iota x)ᴴ = iota (fun k => (x k)ᴴ) from (iota_star x).symm, ← iota_mul]
  rw [h1]
  exact (trace_cfc_iota _ (fun k => Matrix.isHermitian_conjTranspose_mul_self (x k)) _).2

lemma norm_iota (p : ℝ) (hp : 0 < p) (x : K → Matrix L L ℂ) :
    (Nrm p (iota x)) ^ (1 / p) =
      (∑ k, ((Nrm p (x k)) ^ (1 / p)) ^ p) ^ (1 / p) := by
  rw [Nrm_iota]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Real.rpow_mul (Nrm_nonneg p (x k))]
  simp [hp.ne']

lemma peierls (H : Matrix I I ℂ) (hH : H.IsHermitian) (W : Matrix I I ℂ) (hW : star W * W = 1)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    ∑ s, φ ((star W * H * W) s s).re ≤ ∑ i, φ (hH.eigenvalues i) := by
  set U : Matrix I I ℂ := (hH.eigenvectorUnitary : Matrix I I ℂ) with hU
  have hU1 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hU2 : star U * U = 1 := Unitary.coe_star_mul_self _
  set V : Matrix I I ℂ := star U * W with hV
  have hV1 : star V * V = 1 := by
    rw [hV, star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU1, Matrix.one_mul, hW]
  have hV2 : V * star V = 1 := mul_eq_one_comm.mp hV1
  set μ : I → ℝ := hH.eigenvalues
  have hH' : star W * H * W = star V * diagonal (fun s => (μ s : ℂ)) * V := by
    conv_lhs => rw [spectral' hH]
    rw [hV, star_mul, star_star]
    simp only [Matrix.mul_assoc]
    rfl
  set c : I → I → ℝ := fun i s => Complex.normSq (V i s) with hc
  have hc0 : ∀ i s, 0 ≤ c i s := fun i s => Complex.normSq_nonneg _
  have hcs : ∀ s, ∑ i, c i s = 1 := by
    intro s
    have := congrFun (congrFun hV1 s) s
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at this
    have h2 := congrArg Complex.re this
    simp only [Complex.re_sum] at h2
    simpa [hc, Complex.normSq_apply, mul_comm] using h2
  have hci : ∀ i, ∑ s, c i s = 1 := by
    intro i
    have := congrFun (congrFun hV2 i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at this
    have h2 := congrArg Complex.re this
    simp only [Complex.re_sum] at h2
    simpa [hc, Complex.normSq_apply] using h2
  have hent : ∀ s, ((star W * H * W) s s).re = ∑ i, c i s * μ i := by
    intro s
    rw [hH']
    simp [Matrix.mul_apply, Matrix.diagonal_apply, hc, Complex.normSq_apply, Complex.re_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  calc ∑ s, φ ((star W * H * W) s s).re = ∑ s, φ (∑ i, c i s * μ i) := by simp only [hent]
    _ ≤ ∑ s, ∑ i, c i s * φ (μ i) := by
        refine Finset.sum_le_sum fun s _ => ?_
        have := hφ.map_sum_le (t := Finset.univ) (w := fun i => c i s) (p := μ)
          (fun i _ => hc0 i s) (hcs s) (fun _ _ => Set.mem_univ _)
        simpa [smul_eq_mul] using this
    _ = ∑ i, φ (μ i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, hci, one_mul]


def pinch (H : Matrix (K × L) (K × L) ℂ) : Matrix (K × L) (K × L) ℂ :=
  fun i j => if i.1 = j.1 then H i j else 0

def blk (H : Matrix (K × L) (K × L) ℂ) (k : K) : Matrix L L ℂ := fun a b => H (k, a) (k, b)

lemma pinch_eq (H : Matrix (K × L) (K × L) ℂ) : pinch H = iota (blk H) := by
  ext ⟨k, a⟩ ⟨k', b⟩
  simp only [pinch, iota, blk]
  by_cases h : k = k'
  · subst h; rfl
  · simp [h]

lemma blk_herm {H : Matrix (K × L) (K × L) ℂ} (hH : H.IsHermitian) (k : K) : (blk H k).IsHermitian := by
  ext a b
  have := congrFun (congrFun hH (k, a)) (k, b)
  simpa [blk] using this

lemma entry_W' (H : Matrix (K × L) (K × L) ℂ) (U : K → Matrix L L ℂ) (k : K) (a : L) :
    (star (iota U) * H * iota U) (k, a) (k, a) =
    (star (U k) * blk H k * U k) a a := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, iota, Matrix.star_apply, blk]
  simp
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp [apply_ite, ite_mul, Finset.sum_ite_eq']

lemma diag_eig {A : Matrix L L ℂ} (hA : A.IsHermitian) (a : L) :
    (star (hA.eigenvectorUnitary : Matrix L L ℂ) * A * (hA.eigenvectorUnitary : Matrix L L ℂ)) a a
      = (hA.eigenvalues a : ℂ) := by
  have hU1 : (hA.eigenvectorUnitary : Matrix L L ℂ) * star (hA.eigenvectorUnitary : Matrix L L ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have hU2 : star (hA.eigenvectorUnitary : Matrix L L ℂ) * (hA.eigenvectorUnitary : Matrix L L ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have : star (hA.eigenvectorUnitary : Matrix L L ℂ) * A * (hA.eigenvectorUnitary : Matrix L L ℂ) =
      diagonal (fun s => (hA.eigenvalues s : ℂ)) := by
    have h := spectral' hA
    generalize (hA.eigenvectorUnitary : Matrix L L ℂ) = U at h hU1 hU2 ⊢
    generalize (diagonal fun s => (hA.eigenvalues s : ℂ)) = D at h ⊢
    rw [h]
    calc star U * (U * D * star U) * U = (star U * U) * D * (star U * U) := by
          simp only [Matrix.mul_assoc]
      _ = D := by rw [hU2]; simp
  rw [this]; simp

lemma pinch_le {H : Matrix (K × L) (K × L) ℂ} (hH : H.IsHermitian) (φ : ℝ → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) :
    ((cfc φ (pinch H)).trace).re ≤ ((cfc φ H).trace).re := by
  have hy := blk_herm hH
  rw [pinch_eq, (trace_cfc_iota _ hy φ).2, trace_cfc_eig hH]
  have hP := peierls H hH (iota fun k => ((hy k).eigenvectorUnitary : Matrix L L ℂ))
    (iota_unitary _ hy) φ hφ
  have e : ∀ s : K × L, ((star (iota fun k => ((hy k).eigenvectorUnitary : Matrix L L ℂ)) * H *
      iota fun k => ((hy k).eigenvectorUnitary : Matrix L L ℂ)) s s).re = (hy s.1).eigenvalues s.2 := by
    rintro ⟨k, a⟩
    rw [entry_W', diag_eig]
    simp
  calc ∑ k, ((cfc φ (blk H k)).trace).re = ∑ s : K × L, φ ((hy s.1).eigenvalues s.2) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [trace_cfc_eig (hy k)]
    _ = _ := by simp only [← e]
    _ ≤ _ := hP

lemma cfc_sq_trace {M : Matrix I I ℂ} (hM : M.IsHermitian) (g : ℝ → ℝ) :
    ((cfc (fun t : ℝ => g (t ^ 2)) M).trace).re = ((cfc g (M * M)).trace).re := by
  have hfin : (spectrum ℝ M).Finite := by
    rw [hM.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  have hsa : IsSelfAdjoint M := hM
  have h1 : cfc (fun t : ℝ => g (t ^ 2)) M = cfc g (cfc (fun t : ℝ => t ^ 2) M) :=
    cfc_comp g (fun t : ℝ => t ^ 2) M hsa ((hfin.image _).continuousOn g) (hfin.continuousOn _)
  rw [h1, cfc_pow_id M 2 hsa, pow_two]

noncomputable def hfun (p : ℝ) (t : ℝ) : ℝ := Real.rpow (t ^ 2) (p / 2)

lemma hfun_eq (p t : ℝ) : hfun p t = |t| ^ p := by
  unfold hfun
  rw [Real.rpow_eq_pow, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg t)]
  norm_num
  ring_nf

lemma hfun_convex {p : ℝ} (hp : 1 ≤ p) : ConvexOn ℝ Set.univ (hfun p) := by
  have h1 : ConvexOn ℝ (abs '' (Set.univ : Set ℝ)) (fun x : ℝ => x ^ p) := by
    refine (convexOn_rpow hp).subset ?_ ?_
    · rintro _ ⟨x, -, rfl⟩; exact abs_nonneg x
    · have : abs '' (Set.univ : Set ℝ) = Set.Ici 0 := by
        ext y; constructor
        · rintro ⟨x, -, rfl⟩; exact abs_nonneg x
        · intro hy; exact ⟨y, trivial, abs_of_nonneg hy⟩
      rw [this]; exact convex_Ici 0
  have h2 : ConvexOn ℝ Set.univ (fun x : ℝ => |x|) := by
    exact convexOn_univ_norm (E := ℝ)
  have h3 := h1.comp h2 (fun x hx y hy hxy => Real.rpow_le_rpow (by obtain ⟨a, -, rfl⟩ := hx; exact abs_nonneg a) hxy (by linarith))
  convert h3 using 1
  funext t
  simp [hfun_eq]

def dilF (Z : Matrix I I ℂ) : Matrix (I ⊕ I) (I ⊕ I) ℂ := fromBlocks 0 Z Zᴴ 0

lemma dilF_herm (Z : Matrix I I ℂ) : (dilF Z).IsHermitian := by
  unfold Matrix.IsHermitian dilF
  rw [fromBlocks_conjTranspose]; simp

lemma dilF_sq (Z : Matrix I I ℂ) :
    dilF Z * dilF Z = fromBlocks (Z * Zᴴ) 0 0 (Zᴴ * Z) := by
  simp [dilF, fromBlocks_multiply]

lemma Tsum_mul (φ : ℝ → ℝ) (p q : ℂ[X]) (hp : p.Monic) (hq : q.Monic) :
    Tsum φ (p * q) = Tsum φ p + Tsum φ q := by
  unfold Tsum
  rw [Polynomial.roots_mul (hp.mul hq).ne_zero, Multiset.map_add, Multiset.sum_add]

lemma dilF_trace (p : ℝ) (Z : Matrix I I ℂ) :
    ((cfc (hfun p) (dilF Z)).trace).re = 2 * Nrm p Z := by
  refine (cfc_sq_trace (dilF_herm Z) (fun s : ℝ => Real.rpow s (p / 2))).trans ?_
  have hFF : (dilF Z * dilF Z).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, (dilF_herm Z)]
  rw [trace_cfc_re _ hFF, dilF_sq, Matrix.charpoly_fromBlocks_zero₁₂, Tsum_mul _ _ _
    (Matrix.charpoly_monic _) (Matrix.charpoly_monic _), Matrix.charpoly_mul_comm Z Zᴴ]
  unfold Nrm
  rw [trace_cfc_re _ (Matrix.isHermitian_conjTranspose_mul_self Z)]
  ring

def dil (Z : Matrix (K × L) (K × L) ℂ) : Matrix (K × (L ⊕ L)) (K × (L ⊕ L)) ℂ :=
  Matrix.reindex (Equiv.prodSumDistrib K L L).symm (Equiv.prodSumDistrib K L L).symm (dilF Z)

lemma dil_herm (Z : Matrix (K × L) (K × L) ℂ) : (dil Z).IsHermitian := by
  unfold dil
  rw [Matrix.reindex_apply]
  exact (dilF_herm Z).submatrix _

lemma trace_dil (Z : Matrix (K × L) (K × L) ℂ) (φ : ℝ → ℝ) :
    ((cfc φ (dil Z)).trace).re = ((cfc φ (dilF Z)).trace).re := by
  rw [trace_cfc_re _ (dil_herm Z), trace_cfc_re _ (dilF_herm Z)]
  unfold dil
  rw [Matrix.charpoly_reindex]

lemma pinch_dil (Z : Matrix (K × L) (K × L) ℂ) : pinch (dil Z) = dil (pinch Z) := by
  ext ⟨k, a⟩ ⟨k', b⟩
  rcases a with a | a <;> rcases b with b | b <;>
  rcases eq_or_ne k k' with rfl | h <;>
  first
  | (simp [pinch, dil, dilF, Matrix.reindex_apply, Matrix.fromBlocks]; done)
  | (simp [pinch, dil, dilF, h, Ne.symm h, Matrix.reindex_apply, Matrix.fromBlocks]; done)

lemma Nrm_pinch_le {p : ℝ} (hp : 1 ≤ p) (Z : Matrix (K × L) (K × L) ℂ) :
    Nrm p (pinch Z) ≤ Nrm p Z := by
  have h1 := dilF_trace p (pinch Z)
  have h2 := dilF_trace p Z
  rw [← trace_dil] at h1 h2
  rw [← pinch_dil] at h1
  have h3 := pinch_le (dil_herm Z) (hfun p) (hfun_convex hp)
  linarith


lemma schatten_eq (p : ℝ) (hp : 0 < p) (A : Matrix I I ℂ) :
    QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p) A
      = (Nrm p A) ^ (1 / p) := by
  have h1 : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  simp only [QAlgorithms.Papers.Independent.Information100.P50.schattenNorm, h1, if_false,
    ENNReal.toReal_ofReal hp.le, Nrm, Real.rpow_eq_pow]

end E36

open E36
theorem solution (p : ℝ) (hp : 0 < p)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Function.Injective (schattenBlockInclusion n m) ∧
    (∀ x : Fin n → Matrix (Fin m) (Fin m) ℂ,
      QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p)
        (schattenBlockInclusion n m x) =
      finiteLpSize p
        (QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p)) x) ∧
    (1 ≤ p →
      (schattenBlockProjection n m).comp (schattenBlockProjection n m) =
        schattenBlockProjection n m ∧
      LinearMap.range (schattenBlockProjection n m) =
        LinearMap.range (schattenBlockInclusion n m) ∧
      ∀ x : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ,
        QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p)
          (schattenBlockProjection n m x) ≤
        QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p) x) := by
  have hinc : ∀ x, schattenBlockInclusion n m x = iota x := fun x => rfl
  have hproj : ∀ x, schattenBlockProjection n m x = pinch x := fun x => rfl
  have hpi : ∀ x : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ, pinch x = iota (blk x) := pinch_eq
  have hpp : ∀ x : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ, pinch (pinch x) = pinch x := by
    intro x; ext ⟨k, a⟩ ⟨k', b⟩; by_cases h : k = k' <;> simp [pinch, h]
  have hpi2 : ∀ y : Fin n → Matrix (Fin m) (Fin m) ℂ, pinch (iota y) = iota y := by
    intro y; ext ⟨k, a⟩ ⟨k', b⟩; by_cases h : k = k' <;> simp [pinch, iota, h]
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    rw [hinc, hinc] at h
    funext k
    ext a b
    have := congrFun (congrFun h (k, a)) (k, b)
    simpa [iota] using this
  · intro x
    rw [hinc, schatten_eq p hp, finiteLpSize]
    simp only [schatten_eq p hp]
    exact norm_iota p hp x
  · intro hp1
    refine ⟨?_, ?_, ?_⟩
    · ext x : 1
      change schattenBlockProjection n m (schattenBlockProjection n m x) = _
      rw [hproj, hproj, hpp]
    · ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨blk x, by rw [hinc, ← hpi, hproj]⟩
      · rintro ⟨y, rfl⟩
        exact ⟨iota y, by rw [hproj, hinc, hpi2]⟩
    · intro x
      rw [schatten_eq p hp, schatten_eq p hp, hproj]
      exact Real.rpow_le_rpow (Nrm_nonneg _ _) (Nrm_pinch_le hp1 x) (by positivity)

end
