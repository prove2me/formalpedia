-- Prove2me | solution 1 for RobustSpecClust.Round.davis_kahan
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-17T11:13:37.48649+00:00
-- url     : https://prove2.me/submissions/42e449b9-559f-4e34-8147-432d25e2f1d0

import Definitions.Def_RobustSpecClust_Round_Setting

open RobustSpecClust.Round Matrix

namespace DKAux

lemma frobSq_eq_trace {m p : ℕ} (M : Matrix (Fin m) (Fin p) ℝ) : frobSq M = trace (Mᵀ * M) := by
  simp only [frobSq, trace, diag_apply, mul_apply, transpose_apply, sq]
  exact Finset.sum_comm

lemma dot_self_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

lemma dot_mulVec {m p : ℕ} (W : Matrix (Fin m) (Fin p) ℝ) (u : Fin m → ℝ) (z : Fin p → ℝ) :
    u ⬝ᵥ (W *ᵥ z) = (Wᵀ *ᵥ u) ⬝ᵥ z := by
  rw [dotProduct_mulVec, ← mulVec_transpose]

/-- Bessel's inequality for a matrix with orthonormal columns. -/
lemma bessel {m p : ℕ} (W : Matrix (Fin m) (Fin p) ℝ) (hW : Wᵀ * W = 1) (x : Fin m → ℝ) :
    (Wᵀ *ᵥ x) ⬝ᵥ (Wᵀ *ᵥ x) ≤ x ⬝ᵥ x := by
  obtain ⟨z, hz⟩ : ∃ z, z = Wᵀ *ᵥ x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = x - W *ᵥ z := ⟨_, rfl⟩
  have hWy : Wᵀ *ᵥ y = 0 := by
    rw [hy, mulVec_sub, mulVec_mulVec, hW, one_mulVec, hz, sub_self]
  have hx : x = y + W *ᵥ z := by rw [hy, sub_add_cancel]
  have hWz : (W *ᵥ z) ⬝ᵥ (W *ᵥ z) = z ⬝ᵥ z := by
    rw [dot_mulVec, mulVec_mulVec, hW, one_mulVec]
  have hyz : y ⬝ᵥ (W *ᵥ z) = 0 := by rw [dot_mulVec, hWy, zero_dotProduct]
  rw [← hz]
  calc z ⬝ᵥ z ≤ y ⬝ᵥ y + z ⬝ᵥ z := le_add_of_nonneg_left (dot_self_nonneg y)
    _ = (y + W *ᵥ z) ⬝ᵥ (y + W *ᵥ z) := by
        rw [add_dotProduct, dotProduct_add, dotProduct_add, hyz, dotProduct_comm (W *ᵥ z) y, hyz,
          hWz]
        ring
    _ = x ⬝ᵥ x := by rw [← hx]

/-- Trace comparison: if the columns of `U` are eigenvectors of `S` with a gap `g` to the
orthogonal complement, then every orthonormal `W` loses at least `g · ‖sin Θ‖_F²`. -/
lemma trace_gap {n r : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = S)
    (U W : Matrix (Fin n) (Fin r) ℝ) (lam : Fin r → ℝ) (hUU : Uᵀ * U = 1)
    (hSU : S * U = U * diagonal lam) (g : ℝ)
    (hgap : ∀ v : Fin n → ℝ, Uᵀ *ᵥ v = 0 → ∀ k, v ⬝ᵥ (S *ᵥ v) ≤ (lam k - g) * (v ⬝ᵥ v))
    (hWW : Wᵀ * W = 1) :
    g * (r - frobSq (Uᵀ * W)) ≤ trace (Uᵀ * S * U) - trace (Wᵀ * S * W) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp [frobSq, trace]
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ lam
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩)
  -- `c k = ‖Wᵀ u_k‖² ≤ 1`
  have hc1 : ∀ k, ∑ j, (Uᵀ * W) k j ^ 2 ≤ 1 := by
    intro k
    have hb := bessel W hWW (fun i => U i k)
    have h1 : (fun i => U i k) ⬝ᵥ (fun i => U i k) = 1 := by
      have := congrFun (congrFun hUU k) k
      simpa [mul_apply, dotProduct] using this
    have h2 : (Wᵀ *ᵥ fun i => U i k) ⬝ᵥ (Wᵀ *ᵥ fun i => U i k) = ∑ j, (Uᵀ * W) k j ^ 2 := by
      simp only [dotProduct, mulVec, mul_apply, transpose_apply, sq]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1 <;> exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← h2, ← h1]; exact hb
  generalize hC : Uᵀ * W = C at hc1 ⊢
  generalize hY : W - U * C = Y
  have hW : W = U * C + Y := by rw [← hY, add_sub_cancel]
  have hUY : Uᵀ * Y = 0 := by
    rw [← hY, Matrix.mul_sub, ← Matrix.mul_assoc, hUU, Matrix.one_mul, hC, sub_self]
  have hYU : Yᵀ * U = 0 := by
    rw [← transpose_transpose (Yᵀ * U), transpose_mul, transpose_transpose, hUY, transpose_zero]
  have hUS : Uᵀ * S = diagonal lam * Uᵀ := by
    have := congrArg transpose hSU
    rwa [transpose_mul, transpose_mul, hS, diagonal_transpose] at this
  have hUSU : Uᵀ * S * U = diagonal lam := by rw [hUS, Matrix.mul_assoc, hUU, Matrix.mul_one]
  have hUSY : Uᵀ * S * Y = 0 := by rw [hUS, Matrix.mul_assoc, hUY, Matrix.mul_zero]
  have hYSU : Yᵀ * S * U = 0 := by
    rw [Matrix.mul_assoc, hSU, ← Matrix.mul_assoc, hYU, Matrix.zero_mul]
  -- `WᵀSW = Cᵀ Λ C + YᵀSY` and `WᵀW = CᵀC + YᵀY`
  have hWSW : Wᵀ * S * W = Cᵀ * (Uᵀ * S * U) * C + Cᵀ * (Uᵀ * S * Y)
      + (Yᵀ * S * U) * C + Yᵀ * S * Y := by
    rw [hW]
    simp only [transpose_add, transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  have hWW' : Wᵀ * W = Cᵀ * (Uᵀ * U) * C + Cᵀ * (Uᵀ * Y) + (Yᵀ * U) * C + Yᵀ * Y := by
    rw [hW]
    simp only [transpose_add, transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [hUSU, hUSY, hYSU, Matrix.mul_zero, Matrix.zero_mul, add_zero, add_zero] at hWSW
  rw [hUU, hUY, hYU, Matrix.mul_zero, Matrix.zero_mul, add_zero, add_zero, Matrix.mul_one,
    hWW] at hWW'
  -- traces
  have hr1 : (r : ℝ) = ∑ _k : Fin r, (1 : ℝ) := by simp
  have htrY : frobSq Y = r - frobSq C := by
    have := congrArg trace hWW'
    rw [trace_add, trace_one, Fintype.card_fin, ← frobSq_eq_trace, ← frobSq_eq_trace] at this
    linarith
  have htrΛ : trace (Cᵀ * diagonal lam * C) = ∑ k, lam k * ∑ j, C k j ^ 2 := by
    simp only [trace, diag_apply, mul_apply, transpose_apply, diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have htrS : trace (Yᵀ * S * Y) ≤ (lam m - g) * frobSq Y := by
    rw [Matrix.mul_assoc, frobSq_eq_trace, trace, trace, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hv : Uᵀ *ᵥ (fun i => Y i j) = 0 := by
      funext k
      have := congrFun (congrFun hUY k) j
      simpa [mul_apply, mulVec, dotProduct] using this
    have := hgap (fun i => Y i j) hv m
    simpa [diag_apply, mul_apply, mulVec, dotProduct, transpose_apply] using this
  rw [hWSW, trace_add, htrΛ, hUSU, trace_diagonal]
  have hfC : frobSq C = ∑ k, ∑ j, C k j ^ 2 := rfl
  have hkey : 0 ≤ ∑ k, (lam k - lam m) * (1 - ∑ j, C k j ^ 2) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (sub_nonneg.mpr (hm k (Finset.mem_univ k)))
      (sub_nonneg.mpr (hc1 k))
  have hexp : ∑ k, (lam k - lam m) * (1 - ∑ j, C k j ^ 2)
      = ∑ k, lam k - ∑ k, lam k * ∑ j, C k j ^ 2 - lam m * (r - frobSq C) := by
    have h : ∀ k, (lam k - lam m) * (1 - ∑ j, C k j ^ 2)
        = lam k - lam k * ∑ j, C k j ^ 2 - lam m * (1 - ∑ j, C k j ^ 2) := fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, ← hr1, hfC]
  rw [htrY] at htrS
  nlinarith [hkey, hexp, htrS]

/-- The matrix whose columns are the vectors of an orthonormal basis is orthogonal. -/
lemma ob_mem {r : ℕ} (b : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) :
    (Matrix.of fun c i => b i c) ∈ Matrix.orthogonalGroup (Fin r) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  ext i j
  have h := orthonormal_iff_ite.mp b.orthonormal i j
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
  simp only [mul_apply, of_apply, one_apply]
  rw [← h, dotProduct]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-- Orthogonal Procrustes bound: for a contraction `N` some orthogonal `O` has
`tr(Oᵀ N) ≥ ‖N‖_F²`. -/
lemma procrustes {r : ℕ} (N : Matrix (Fin r) (Fin r) ℝ)
    (hN : ∀ x : Fin r → ℝ, (N *ᵥ x) ⬝ᵥ (N *ᵥ x) ≤ x ⬝ᵥ x) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin r) ℝ, frobSq N ≤ trace (Oᵀ * N) := by
  have hA : (Nᵀ * N).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_transpose]
  set v := hA.eigenvectorBasis with hvdef
  have hv : ∀ i j, (⇑(v i) : Fin r → ℝ) ⬝ᵥ ⇑(v j) = if i = j then 1 else 0 := by
    intro i j
    have h := orthonormal_iff_ite.mp v.orthonormal i j
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] at h
    exact h
  have heig : ∀ j, (Nᵀ * N) *ᵥ ⇑(v j) = hA.eigenvalues j • ⇑(v j) :=
    hA.mulVec_eigenvectorBasis
  have hNN : ∀ i j, (N *ᵥ ⇑(v i)) ⬝ᵥ (N *ᵥ ⇑(v j))
      = hA.eigenvalues i * (if i = j then 1 else 0) := by
    intro i j
    rw [dot_mulVec, mulVec_mulVec, heig, smul_dotProduct, hv, smul_eq_mul]
  -- the images `f i = N v_i` are pairwise orthogonal
  let f : Fin r → EuclideanSpace ℝ (Fin r) := fun i => WithLp.toLp 2 (N *ᵥ ⇑(v i))
  have hff : ∀ i j, inner ℝ (f i) (f j) = (N *ᵥ ⇑(v i)) ⬝ᵥ (N *ᵥ ⇑(v j)) := by
    intro i j
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  have horth : Pairwise fun i j => inner ℝ (f i) (f j) = 0 := by
    intro i j hij
    rw [hff, hNN, if_neg hij, mul_zero]
  have hnorm2 : ∀ i, ‖f i‖ ^ 2 = (N *ᵥ ⇑(v i)) ⬝ᵥ (N *ᵥ ⇑(v i)) := by
    intro i
    rw [← real_inner_self_eq_norm_sq, hff]
  have hle1 : ∀ i, ‖f i‖ ≤ 1 := by
    intro i
    have h1 := hN ⇑(v i)
    rw [hv, if_pos rfl, ← hnorm2] at h1
    nlinarith [norm_nonneg (f i)]
  -- complete the normalised images to an orthonormal basis
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin r)) f
  have hbf : ∀ i, inner ℝ (b i) (f i) = ‖f i‖ := by
    intro i
    by_cases h0 : f i = 0
    · rw [h0, inner_zero_right, norm_zero]
    · have hb : b i = (‖f i‖⁻¹ : ℝ) • f i :=
        InnerProductSpace.gramSchmidtOrthonormalBasis_apply_of_orthogonal _ horth h0
      rw [hb, real_inner_smul_left, real_inner_self_eq_norm_sq]
      have : ‖f i‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      field_simp
  refine ⟨Matrix.of (fun c i => b i c) * star (Matrix.of fun a i => v i a),
    Submonoid.mul_mem _ (ob_mem b) (Unitary.star_mem (ob_mem v)), ?_⟩
  have htr : trace ((Matrix.of (fun c i => b i c) * star (Matrix.of fun a i => v i a))ᵀ * N)
      = ∑ i, inner ℝ (b i) (f i) := by
    rw [transpose_mul, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      transpose_transpose, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
    simp only [trace, diag_apply, mul_apply, transpose_apply, of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial]
    simp only [dotProduct, mulVec]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have hfro : frobSq N = ∑ i, ‖f i‖ ^ 2 := by
    rw [frobSq_eq_trace, hA.trace_eq_sum_eigenvalues]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hnorm2, hNN, if_pos rfl, mul_one]
    simp
  rw [htr, hfro]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hbf]
  exact pow_le_of_le_one (norm_nonneg _) (hle1 i) two_ne_zero

/-- Cauchy–Schwarz for the Frobenius inner product. -/
lemma frob_cs {m p : ℕ} (A B : Matrix (Fin m) (Fin p) ℝ) :
    (∑ i, ∑ j, A i j * B i j) ^ 2 ≤ frobSq A * frobSq B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin p))
    (fun x => A x.1 x.2) (fun x => B x.1 x.2)
  simpa only [frobSq, Fintype.sum_prod_type] using h

lemma frobSq_transpose {m p : ℕ} (M : Matrix (Fin m) (Fin p) ℝ) : frobSq Mᵀ = frobSq M := by
  simp only [frobSq, transpose_apply]
  exact Finset.sum_comm

lemma frobSq_nonneg {m p : ℕ} (M : Matrix (Fin m) (Fin p) ℝ) : 0 ≤ frobSq M :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

end DKAux

open DKAux in
theorem solution {n r : ℕ} (S Sh : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = S) (hSh : Shᵀ = Sh)
    (U Uh : Matrix (Fin n) (Fin r) ℝ) (lam : Fin r → ℝ) (hU : IsTopEigvecsWith S U lam)
    (g : ℝ) (hg : 0 < g)
    (hgap : ∀ v : Fin n → ℝ, Uᵀ *ᵥ v = 0 → ∀ k, v ⬝ᵥ (S *ᵥ v) ≤ (lam k - g) * (v ⬝ᵥ v))
    (hUh : IsTopEigvecs Sh Uh) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin r) ℝ,
      Real.sqrt (frobSq (U - Uh * O)) ≤ 2 ^ (3 / 2 : ℝ) * Real.sqrt (frobSq (Sh - S)) / g := by
  obtain ⟨hUU, hSU, -⟩ := hU
  obtain ⟨lamh, hUhU, hShU, hgaph⟩ := hUh
  -- the two trace comparisons
  have A1 := trace_gap S hS U Uh lam hUU hSU g hgap hUhU
  have A2 := trace_gap Sh hSh Uh U lamh hUhU hShU 0
    (fun v hv k => by rw [sub_zero]; exact hgaph v hv k) hUU
  rw [zero_mul] at A2
  have hCT : frobSq (Uhᵀ * U) = frobSq (Uᵀ * Uh) := by
    rw [← frobSq_transpose (Uᵀ * Uh), transpose_mul, transpose_transpose]
  -- `D = ÛÛᵀ − UUᵀ`, `‖D‖_F² = 2 (r − ‖UᵀÛ‖_F²)`
  have hDsym : (Uh * Uhᵀ - U * Uᵀ)ᵀ = Uh * Uhᵀ - U * Uᵀ := by
    rw [transpose_sub, transpose_mul, transpose_mul, transpose_transpose, transpose_transpose]
  have t1 : trace (Uh * Uhᵀ * (Uh * Uhᵀ)) = r := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uhᵀ, hUhU, Matrix.one_mul, trace_mul_comm, hUhU,
      trace_one, Fintype.card_fin]
  have t2 : trace (U * Uᵀ * (U * Uᵀ)) = r := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hUU, Matrix.one_mul, trace_mul_comm, hUU,
      trace_one, Fintype.card_fin]
  have t3 : trace (Uh * Uhᵀ * (U * Uᵀ)) = frobSq (Uᵀ * Uh) := by
    calc trace (Uh * Uhᵀ * (U * Uᵀ)) = trace (Uh * (Uhᵀ * U * Uᵀ)) := by
          simp only [Matrix.mul_assoc]
      _ = trace (Uhᵀ * U * Uᵀ * Uh) := trace_mul_comm _ _
      _ = frobSq (Uᵀ * Uh) := by
          rw [frobSq_eq_trace, transpose_mul, transpose_transpose]
          simp only [Matrix.mul_assoc]
  have t4 : trace (U * Uᵀ * (Uh * Uhᵀ)) = frobSq (Uᵀ * Uh) := by rw [trace_mul_comm, t3]
  have hDfro : frobSq (Uh * Uhᵀ - U * Uᵀ) = 2 * ((r : ℝ) - frobSq (Uᵀ * Uh)) := by
    rw [frobSq_eq_trace, hDsym, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, trace_sub,
      trace_sub, trace_sub, t1, t2, t3, t4]
    ring
  have hs0 : 0 ≤ (r : ℝ) - frobSq (Uᵀ * Uh) := by
    have := frobSq_nonneg (Uh * Uhᵀ - U * Uᵀ)
    linarith
  -- `tr(ÛᵀEÛ) − tr(UᵀEU) = ⟨E, D⟩`
  have hX : trace (Uhᵀ * Sh * Uh) - trace (Uᵀ * Sh * U)
      + (trace (Uᵀ * S * U) - trace (Uhᵀ * S * Uh))
      = ∑ i, ∑ j, (Sh - S) i j * (Uh * Uhᵀ - U * Uᵀ) i j := by
    have hc : ∀ (V : Matrix (Fin n) (Fin r) ℝ) (M : Matrix (Fin n) (Fin n) ℝ),
        trace (Vᵀ * M * V) = trace (M * (V * Vᵀ)) := by
      intro V M
      rw [trace_mul_comm, ← Matrix.mul_assoc, trace_mul_comm]
    have hE : ∑ i, ∑ j, (Sh - S) i j * (Uh * Uhᵀ - U * Uᵀ) i j
        = trace ((Sh - S) * (Uh * Uhᵀ - U * Uᵀ)) := by
      simp only [trace, diag_apply, mul_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← transpose_apply (Uh * Uhᵀ - U * Uᵀ) i j, hDsym]
    rw [hE, hc, hc, hc, hc, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, trace_sub, trace_sub,
      trace_sub]
    ring
  have hcs := frob_cs (Sh - S) (Uh * Uhᵀ - U * Uᵀ)
  rw [hDfro, ← hX] at hcs
  -- `s² g² ≤ 2 ‖E‖_F²`
  have hF0 := frobSq_nonneg (Sh - S)
  have hsg : ((r : ℝ) - frobSq (Uᵀ * Uh)) * g ^ 2 ≤ 2 * frobSq (Sh - S) := by
    rcases hs0.lt_or_eq with hs | hs
    · have hgs : 0 ≤ g * ((r : ℝ) - frobSq (Uᵀ * Uh)) := mul_nonneg hg.le hs0
      have hle : g * ((r : ℝ) - frobSq (Uᵀ * Uh)) ≤ trace (Uhᵀ * Sh * Uh) - trace (Uᵀ * Sh * U)
          + (trace (Uᵀ * S * U) - trace (Uhᵀ * S * Uh)) := by linarith
      have h1 := pow_le_pow_left₀ hgs hle 2
      have h2 := h1.trans hcs
      have h3 : (((r : ℝ) - frobSq (Uᵀ * Uh)) * g ^ 2) * ((r : ℝ) - frobSq (Uᵀ * Uh))
          ≤ (2 * frobSq (Sh - S)) * ((r : ℝ) - frobSq (Uᵀ * Uh)) := by nlinarith
      exact le_of_mul_le_mul_right h3 hs
    · rw [← hs, zero_mul]; linarith
  -- Procrustes
  have hN : ∀ x : Fin r → ℝ, ((Uhᵀ * U) *ᵥ x) ⬝ᵥ ((Uhᵀ * U) *ᵥ x) ≤ x ⬝ᵥ x := by
    intro x
    rw [← mulVec_mulVec]
    have hb := bessel Uh hUhU (U *ᵥ x)
    have hUx : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
      rw [dot_mulVec, mulVec_mulVec, hUU, one_mulVec]
    linarith
  obtain ⟨O, hO, hOtr⟩ := procrustes (Uhᵀ * U) hN
  have hOO : Oᵀ * O = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff' (Fin r) ℝ).mp hO
  have hdist : frobSq (U - Uh * O) = 2 * r - 2 * trace (Oᵀ * (Uhᵀ * U)) := by
    have e1 : trace (Oᵀ * Uhᵀ * (Uh * O)) = r := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uhᵀ, hUhU, Matrix.one_mul, hOO, trace_one,
        Fintype.card_fin]
    have e2 : trace (Uᵀ * (Uh * O)) = trace (Oᵀ * (Uhᵀ * U)) := by
      rw [← trace_transpose, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    have e3 : trace (Oᵀ * Uhᵀ * U) = trace (Oᵀ * (Uhᵀ * U)) := by rw [Matrix.mul_assoc]
    rw [frobSq_eq_trace, transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, trace_sub, trace_sub, trace_sub, hUU, e1, e2, e3, trace_one,
      Fintype.card_fin]
    ring
  refine ⟨O, hO, ?_⟩
  have hc : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hy0 : 0 ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (frobSq (Sh - S)) / g := by positivity
  have hy2 : ((2 : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (frobSq (Sh - S)) / g) ^ 2
      = 8 * frobSq (Sh - S) / g ^ 2 := by
    rw [div_pow, mul_pow, hc, Real.sq_sqrt hF0]
  have hmain : frobSq (U - Uh * O) ≤ 8 * frobSq (Sh - S) / g ^ 2 := by
    rw [hdist, le_div_iff₀ (by positivity)]
    rw [hCT] at hOtr
    nlinarith
  calc Real.sqrt (frobSq (U - Uh * O))
      ≤ Real.sqrt (((2 : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (frobSq (Sh - S)) / g) ^ 2) := by
        rw [hy2]; exact Real.sqrt_le_sqrt hmain
    _ = (2 : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (frobSq (Sh - S)) / g := Real.sqrt_sq hy0
