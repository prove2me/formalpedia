-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.spectralOverlapError
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:43:55.327644+00:00
-- url     : https://prove2.me/submissions/0337e132-5974-4584-aaa5-d7a060e7e555

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open Finset
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P53

lemma p53s204_sumP {N : ℕ} (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ∑ j, pureDensity (b j) = 1 := by
  ext u v
  have h := b.sum_inner_mul_inner (EuclideanSpace.single u (1:ℂ)) (EuclideanSpace.single v (1:ℂ))
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] at h
  simp only [Matrix.sum_apply, pureDensity, Matrix.of_apply, Matrix.one_apply]
  rw [h]; by_cases huv : u = v <;> simp [huv, eq_comm]

lemma p53s204_unit {N : ℕ} (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (j : Fin N) :
    ∑ w, conj (b j w) * b j w = 1 := by
  have h := orthonormal_iff_ite.mp b.orthonormal j j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [if_true] at h
  rw [← h]; simp [dotProduct, mul_comm]

lemma p53s204_psdP {N : ℕ} (v : EuclideanSpace ℂ (Fin N)) : (pureDensity v).PosSemidef := by
  have : pureDensity v = Matrix.vecMulVec (⇑v) (star ⇑v) := by
    ext x y; simp [pureDensity, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

lemma p53s204_sum_psd {N : ℕ} {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

lemma p53s204_sqrt_psd {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma p53s204_sqrt_mul_sqrt {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix (Fin N) (Fin N) ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma p53s204_tr_psd_mul {N : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace.re := by
  have hR : (cfc Real.sqrt Q)ᴴ = cfc Real.sqrt Q := (p53s204_sqrt_psd Q).1.eq
  have h := (hP.conjTranspose_mul_mul_same (cfc Real.sqrt Q)).trace_nonneg
  rw [hR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, p53s204_sqrt_mul_sqrt hQ,
    Matrix.trace_mul_comm] at h
  exact (Complex.nonneg_iff.mp h).1

lemma p53s204_proj_sqrt {h : ℕ} (P : Matrix (Fin h) (Fin h) ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) (r : ℝ) (hr : 0 ≤ r) :
    cfc Real.sqrt (r • P) = Real.sqrt r • P := by
  have hsa : IsSelfAdjoint P := hP
  have hspec : ∀ x ∈ spectrum ℝ P, x = 0 ∨ x = 1 := by
    have h1 : cfc (fun x : ℝ => x ^ 2) P = cfc (fun x : ℝ => x) P := by
      rw [cfc_pow_id (R := ℝ) P 2 hsa, cfc_id' (R := ℝ) (a := P) (ha := hsa), sq, hPP]
    have := eqOn_of_cfc_eq_cfc h1 (ha := hsa)
    intro x hx
    have hx2 : x ^ 2 = x := this hx
    have : x * (x - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h0 | h0
    · left; exact h0
    · right; linarith
  rw [← cfc_comp_const_mul r Real.sqrt P (ha := hsa)]
  rw [cfc_congr (g := fun x => Real.sqrt r * x), cfc_const_mul_id (R := ℝ) _ P (ha := hsa)]
  intro x hx
  rcases hspec x hx with rfl | rfl <;> simp

lemma p53s204_F2 {h : ℕ} (ψ : EuclideanSpace ℂ (Fin h)) (hψ : ∑ b, conj (ψ b) * ψ b = 1)
    (σ : Matrix (Fin h) (Fin h) ℂ) (hσ : σ.PosSemidef) :
    rootFidelity (pureDensity ψ) σ ^ 2 = (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re := by
  set P := pureDensity ψ with hPdef
  have hP : P.IsHermitian := by
    ext x y; simp [P, pureDensity, Matrix.conjTranspose_apply, mul_comm]
  have hPP : P * P = P := by
    ext x y
    simp only [P, pureDensity, Matrix.mul_apply, Matrix.of_apply]
    calc ∑ b, ψ x * conj (ψ b) * (ψ b * conj (ψ y))
        = ψ x * conj (ψ y) * ∑ b, conj (ψ b) * ψ b := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
      _ = ψ x * conj (ψ y) := by rw [hψ, mul_one]
  set c := ∑ a, ∑ b, conj (ψ a) * σ a b * ψ b with hc
  have hc0 : 0 ≤ c := by
    have := hσ.dotProduct_mulVec_nonneg (⇑ψ)
    convert this using 1
    simp only [c, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Complex.nonneg_iff] at hc0
  have hcr : c = ((c.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hc0.2])
  have hPsP : P * σ * P = (c.re : ℝ) • P := by
    ext x y
    rw [← Complex.coe_smul, ← hcr]
    simp only [P, pureDensity, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      c, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hsq : cfc Real.sqrt P = P := by
    have := p53s204_proj_sqrt P hP hPP 1 zero_le_one
    simpa using this
  have htrP : P.trace = 1 := by
    simp only [P, pureDensity, Matrix.trace, Matrix.diag, Matrix.of_apply]
    rw [← hψ]; refine Finset.sum_congr rfl fun b _ => ?_; ring
  unfold rootFidelity
  rw [hsq, hPsP, p53s204_proj_sqrt P hP hPP _ hc0.1, Matrix.trace_smul, htrP]
  simp [Real.sq_sqrt hc0.1]

lemma p53s204_fid {N : ℕ} (e f : EuclideanSpace ℂ (Fin N)) (he : ∑ b, conj (e b) * e b = 1) :
    fidelity (pureDensity e) (pureDensity f) = (pureDensity e * pureDensity f).trace.re := by
  unfold fidelity
  rw [p53s204_F2 e he _ (p53s204_psdP f)]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma p53s204_eig_nonneg {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef)
    (s : SpectralData A) (k : Fin N) : 0 ≤ s.value k := by
  have hAe : ∀ u w, A u w = ∑ m, (s.value m : ℂ) * (s.basis m u * conj (s.basis m w)) := by
    intro u w
    have := congrFun (congrFun s.reconstruct u) w
    rw [this]; simp [Matrix.sum_apply, pureDensity]
  have hm : A.mulVec ⇑(s.basis k) = (s.value k : ℂ) • ⇑(s.basis k) := by
    ext u
    simp only [Matrix.mulVec, dotProduct, hAe, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ m, ∑ w, (s.value m : ℂ) * ((s.basis m) u * conj ((s.basis m) w)) * s.basis k w =
        (s.value m : ℂ) * s.basis m u * (if m = k then 1 else 0) := by
      intro m
      have h := orthonormal_iff_ite.mp s.basis.orthonormal m k
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h
      rw [← h]
      simp only [dotProduct, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring
    simp_rw [this]
    simp
  have key : star (⇑(s.basis k)) ⬝ᵥ A.mulVec ⇑(s.basis k) = (s.value k : ℂ) := by
    rw [hm, dotProduct_smul]
    have := p53s204_unit s.basis k
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, smul_eq_mul] at this ⊢
    rw [this, mul_one]
  have h := hA.dotProduct_mulVec_nonneg (⇑(s.basis k))
  rw [key] at h
  exact_mod_cast h

lemma p53s204_lin {N : ℕ} (c : Fin N → ℝ) (P : Fin N → Matrix (Fin N) (Fin N) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    ∑ j, c j * (P j * X).trace.re = ((∑ j, (c j : ℂ) • P j) * X).trace.re := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma p53s204_add {N : ℕ} (X U V : Matrix (Fin N) (Fin N) ℂ) :
    (X * (U + V)).trace.re = (X * U).trace.re + (X * V).trace.re := by
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

lemma p53s204_pair {N : ℕ} (e f : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (a b : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ l, 0 ≤ b l)
    (Z : Matrix (Fin N) (Fin N) ℂ) (hZ : Z.IsHermitian) (hZ2 : (1 - Z * Z).PosSemidef) :
    ∑ j, ∑ l, min (a j) (b l) * (pureDensity (e j) * pureDensity (f l)).trace.re ≤
      ((∑ j, (a j : ℂ) • pureDensity (e j)) * (1 - Z)).trace.re +
        ((∑ l, (b l : ℂ) • pureDensity (f l)) * (1 + Z)).trace.re := by
  set P := fun j => pureDensity (e j) with hP
  set Q := fun l => pureDensity (f l) with hQ
  have hPp : ∀ j, (P j).PosSemidef := fun j => p53s204_psdP _
  have hQp : ∀ l, (Q l).PosSemidef := fun l => p53s204_psdP _
  have hsP : ∑ j, P j = 1 := p53s204_sumP e
  have hsQ : ∑ l, Q l = 1 := p53s204_sumP f
  have hW : ∀ X : Matrix (Fin N) (Fin N) ℂ, X.IsHermitian → ∀ l, (X * Q l * X).PosSemidef := by
    intro X hX l
    have := (hQp l).conjTranspose_mul_mul_same X
    rwa [hX.eq] at this
  have hS : (1 - Z).IsHermitian := Matrix.isHermitian_one.sub hZ
  have hT : (1 + Z).IsHermitian := Matrix.isHermitian_one.add hZ
  set x : Fin N → Fin N → ℝ := fun j l => (P j * ((1 - Z) * Q l * (1 - Z))).trace.re / 2 with hx
  set y : Fin N → Fin N → ℝ := fun j l => (P j * ((1 + Z) * Q l * (1 + Z))).trace.re / 2 with hy
  have hx0 : ∀ j l, 0 ≤ x j l := fun j l => by
    have := p53s204_tr_psd_mul (hPp j) (hW _ hS l); simp only [hx]; linarith
  have hy0 : ∀ j l, 0 ≤ y j l := fun j l => by
    have := p53s204_tr_psd_mul (hPp j) (hW _ hT l); simp only [hy]; linarith
  have step1 : ∀ j l, (P j * Q l).trace.re ≤ x j l + y j l := by
    intro j l
    have eq : (1 - Z) * Q l * (1 - Z) + (1 + Z) * Q l * (1 + Z) =
        Q l + Q l + (Z * Q l * Z + Z * Q l * Z) := by noncomm_ring
    have h := congrArg (fun X => (P j * X).trace.re) eq
    simp only [p53s204_add] at h
    have h0 := p53s204_tr_psd_mul (hPp j) (hW _ hZ l)
    simp only [hx, hy]
    linarith
  have step2 : ∀ j l, min (a j) (b l) * (P j * Q l).trace.re ≤ a j * x j l + b l * y j l := by
    intro j l
    have hm0 : 0 ≤ min (a j) (b l) := le_min (ha j) (hb l)
    have e1 := mul_le_mul_of_nonneg_left (step1 j l) hm0
    have e2 := mul_le_mul_of_nonneg_right (min_le_left (a j) (b l)) (hx0 j l)
    have e3 := mul_le_mul_of_nonneg_right (min_le_right (a j) (b l)) (hy0 j l)
    nlinarith
  have hsumL : ∀ X Y : Matrix (Fin N) (Fin N) ℂ,
      ∑ l, (X * (Y * Q l * Y)).trace.re = (X * (Y * Y)).trace.re := by
    intro X Y
    rw [← Complex.re_sum, ← Matrix.trace_sum]
    congr 2
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, hsQ, mul_one]
  have hsumR : ∀ W : Matrix (Fin N) (Fin N) ℂ, ∑ j, (P j * W).trace.re = W.trace.re := by
    intro W
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hsP, one_mul]
  have hA : ∑ j, ∑ l, a j * x j l =
      ((∑ j, (a j : ℂ) • P j) * ((1 - Z) * (1 - Z))).trace.re / 2 := by
    rw [← p53s204_lin, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum]
    simp only [hx]
    rw [← Finset.sum_div, hsumL]; ring
  have hB : ∑ j, ∑ l, b l * y j l =
      ((∑ l, (b l : ℂ) • Q l) * ((1 + Z) * (1 + Z))).trace.re / 2 := by
    rw [Finset.sum_comm, ← p53s204_lin, Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_sum]
    simp only [hy]
    rw [← Finset.sum_div, hsumR]
    rw [show ((1 + Z) * Q l * (1 + Z)).trace = (Q l * ((1 + Z) * (1 + Z))).trace by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]]
    ring
  have hApsd : (∑ j, (a j : ℂ) • P j).PosSemidef :=
    p53s204_sum_psd _ _ fun j => (hPp j).smul (by exact_mod_cast ha j)
  have hBpsd : (∑ l, (b l : ℂ) • Q l).PosSemidef :=
    p53s204_sum_psd _ _ fun l => (hQp l).smul (by exact_mod_cast hb l)
  have hA2 : ((∑ j, (a j : ℂ) • P j) * ((1 - Z) * (1 - Z))).trace.re ≤
      2 * ((∑ j, (a j : ℂ) • P j) * (1 - Z)).trace.re := by
    have eq : (1 - Z) * (1 - Z) + (1 - Z * Z) = (1 - Z) + (1 - Z) := by noncomm_ring
    have h := p53s204_add (∑ j, (a j : ℂ) • P j) ((1 - Z) * (1 - Z)) (1 - Z * Z)
    have h' := p53s204_add (∑ j, (a j : ℂ) • P j) (1 - Z) (1 - Z)
    rw [eq] at h
    have h0 := p53s204_tr_psd_mul hApsd hZ2
    linarith
  have hB2 : ((∑ l, (b l : ℂ) • Q l) * ((1 + Z) * (1 + Z))).trace.re ≤
      2 * ((∑ l, (b l : ℂ) • Q l) * (1 + Z)).trace.re := by
    have eq : (1 + Z) * (1 + Z) + (1 - Z * Z) = (1 + Z) + (1 + Z) := by noncomm_ring
    have h := p53s204_add (∑ l, (b l : ℂ) • Q l) ((1 + Z) * (1 + Z)) (1 - Z * Z)
    have h' := p53s204_add (∑ l, (b l : ℂ) • Q l) (1 + Z) (1 + Z)
    rw [eq] at h
    have h0 := p53s204_tr_psd_mul hBpsd hZ2
    linarith
  calc ∑ j, ∑ l, min (a j) (b l) * (pureDensity (e j) * pureDensity (f l)).trace.re
      ≤ ∑ j, ∑ l, (a j * x j l + b l * y j l) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => step2 j l
    _ = ∑ j, ∑ l, a j * x j l + ∑ j, ∑ l, b l * y j l := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_add_distrib
    _ ≤ _ := by rw [hA, hB]; linarith

lemma p53s204_pair_sum {M : ℕ} (g : Fin M → Fin M → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (g i j + g j i) =
      ∑ i, ∑ j, g i j - ∑ i, g i i := by
  simp only [Finset.sum_filter]
  have h1 : ∑ i : Fin M, ∑ j : Fin M, (if i < j then g i j + g j i else 0) =
      ∑ i : Fin M, ∑ j : Fin M, (if i < j then g i j else 0) +
        ∑ i : Fin M, ∑ j : Fin M, (if j < i then g i j else 0) := by
    rw [Finset.sum_comm (f := fun i j => if j < i then g i j else 0), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [h1, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (s := Finset.univ) (a := i) (fun j => g i j) (Finset.mem_univ i)]
  simp only [lt_irrefl, if_false, add_zero]
  have : ∀ j ∈ Finset.univ.erase i,
      ((if i < j then g i j else 0) + if j < i then g i j else 0) = g i j := by
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h, not_lt.mpr h.le]
  rw [Finset.sum_congr rfl this]
  ring

lemma p53s204_one_sub_sq {N : ℕ} {Z : Matrix (Fin N) (Fin N) ℂ} (hZ : Z.IsHermitian)
    (h1 : (1 - Z).PosSemidef) (h2 : (1 + Z).PosSemidef) : (1 - Z * Z).PosSemidef := by
  have hsa : IsSelfAdjoint Z := hZ
  have hle : ∀ t ∈ spectrum ℝ Z, t ≤ 1 := by
    have : Z ≤ algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) 1 := by
      rw [map_one, ← sub_nonneg, Matrix.nonneg_iff_posSemidef]; exact h1
    exact (le_algebraMap_iff_spectrum_le).mp this
  have hge : ∀ t ∈ spectrum ℝ Z, -1 ≤ t := by
    have : algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) (-1) ≤ Z := by
      rw [map_neg, map_one, ← sub_nonneg, sub_neg_eq_add, add_comm, Matrix.nonneg_iff_posSemidef]
      exact h2
    exact (algebraMap_le_iff_le_spectrum).mp this
  have e : 1 - Z * Z = cfc (fun t : ℝ => 1 - t * t) Z := by
    rw [cfc_sub (fun _ => (1 : ℝ)) (fun t : ℝ => t * t) Z, cfc_const_one ℝ Z,
      cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) Z, cfc_id' ℝ Z]
  rw [e, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro t ht
  nlinarith [hle t ht, hge t ht]

lemma p53s204_povm_contr {M N : ℕ} (D : Fin M → Matrix (Fin N) (Fin N) ℂ)
    (hD : ∀ k, (D k).PosSemidef) (hs : ∑ k, D k = 1) (i j : Fin M) :
    (D i - D j).IsHermitian ∧ (1 - (D i - D j) * (D i - D j)).PosSemidef := by
  have hH : (D i - D j).IsHermitian := (hD i).1.sub (hD j).1
  refine ⟨hH, p53s204_one_sub_sq hH ?_ ?_⟩
  · have : 1 - (D i - D j) = (∑ k ∈ Finset.univ.erase i, D k) + D j := by
      rw [← hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; abel
    rw [this]; exact (p53s204_sum_psd _ _ hD).add (hD j)
  · have : 1 + (D i - D j) = (∑ k ∈ Finset.univ.erase j, D k) + D i := by
      rw [← hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]; abel
    rw [this]; exact (p53s204_sum_psd _ _ hD).add (hD i)

lemma p53s204_bound {M N : ℕ} (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (s : ∀ i, SpectralData (rho i)) (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) :
    (pairSum fun i k => ∑ j : Fin N, ∑ l : Fin N,
      min (p i * (s i).value j) (p k * (s k).value l) *
        fidelity (pureDensity ((s i).basis j)) (pureDensity ((s k).basis l))) ≤
      (M : ℝ) * (1 - ∑ j, p j * effectProb (D j) (rho j)) := by
  set t : Fin M → Fin M → ℝ := fun k l => (D k * ((p l : ℂ) • rho l)).trace.re with ht
  have hsucc : ∑ j, p j * effectProb (D j) (rho j) = ∑ i, t i i := by
    unfold effectProb
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ht, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hA : ∀ i, (p i : ℂ) • rho i =
      ∑ j, ((p i * (s i).value j : ℝ) : ℂ) • pureDensity ((s i).basis j) := by
    intro i
    conv_lhs => rw [(s i).reconstruct]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]; push_cast; rfl
  have htr : ∀ i, ((p i : ℂ) • rho i).trace.re = p i := by
    intro i; rw [Matrix.trace_smul, (hrho i).2]; simp
  have hcomm : ∀ i k, ((p i : ℂ) • rho i * D k).trace.re = t k i := by
    intro i k; simp only [ht]; rw [Matrix.trace_mul_comm]
  set g : Fin M → Fin M → ℝ := fun i k => p i - t i i + t k i with hg
  have hterm : ∀ i k, (∑ j : Fin N, ∑ l : Fin N,
      min (p i * (s i).value j) (p k * (s k).value l) *
        fidelity (pureDensity ((s i).basis j)) (pureDensity ((s k).basis l))) ≤ g i k + g k i := by
    intro i k
    have hfid : ∀ j l, fidelity (pureDensity ((s i).basis j)) (pureDensity ((s k).basis l)) =
        (pureDensity ((s i).basis j) * pureDensity ((s k).basis l)).trace.re :=
      fun j l => p53s204_fid _ _ (p53s204_unit _ _)
    simp_rw [hfid]
    obtain ⟨hZ, hZ2⟩ := p53s204_povm_contr D hD.1 hD.2 i k
    have h := p53s204_pair (s i).basis (s k).basis (fun j => p i * (s i).value j)
      (fun l => p k * (s k).value l)
      (fun j => mul_nonneg (hp.1 i) (p53s204_eig_nonneg (hrho i).1 _ j))
      (fun l => mul_nonneg (hp.1 k) (p53s204_eig_nonneg (hrho k).1 _ l)) _ hZ hZ2
    rw [← hA, ← hA] at h
    refine h.trans (le_of_eq ?_)
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one,
      Matrix.mul_one]
    simp only [Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re, htr, hcomm, hg]
    ring
  have hsumk : ∀ i, ∑ k, t k i = p i := by
    intro i
    simp only [ht]
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hD.2, Matrix.one_mul, htr]
  calc _ ≤ ∑ i, ∑ k ∈ Finset.univ.filter (fun k => i < k), (g i k + g k i) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hterm i k
    _ = ∑ i, ∑ k, g i k - ∑ i, g i i := p53s204_pair_sum g
    _ = _ := by
      simp only [hg, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsumk, sub_self, add_zero]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hsucc, ← Finset.mul_sum, ← Finset.mul_sum, hp.2]
      ring

end

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P53 in
open scoped Matrix ComplexConjugate ComplexOrder in
open Finset in
theorem solution {M N : ℕ} (hM : 2 ≤ M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (s : ∀ i, SpectralData (rho i)) :
    (pairSum fun i k => ∑ j : Fin N, ∑ l : Fin N,
      min (p i * (s i).value j) (p k * (s k).value l) *
        fidelity (pureDensity ((s i).basis j)) (pureDensity ((s k).basis l))) /
      (2 * ((M : ℝ) - 1)) ≤ 1 - mixedOptSuccess p rho := by
  set X := (pairSum fun i k => ∑ j : Fin N, ∑ l : Fin N,
      min (p i * (s i).value j) (p k * (s k).value l) *
        fidelity (pureDensity ((s i).basis j)) (pureDensity ((s k).basis l))) with hX
  have hX0 : 0 ≤ X := by
    simp only [hX, pairSum]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => mul_nonneg ?_ ?_
    · exact le_min (mul_nonneg (hp.1 i) (p53s204_eig_nonneg (hrho i).1 _ j))
        (mul_nonneg (hp.1 k) (p53s204_eig_nonneg (hrho k).1 _ l))
    · unfold fidelity; positivity
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM' : (0 : ℝ) < 2 * ((M : ℝ) - 1) := by linarith
  have i0 : Fin M := ⟨0, by omega⟩
  have : Nonempty {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D} := by
    refine ⟨⟨fun j => if j = i0 then 1 else 0, ?_, ?_⟩⟩
    · intro j; dsimp only; split_ifs
      · exact Matrix.PosSemidef.one
      · exact Matrix.PosSemidef.zero
    · simp
  have hle : mixedOptSuccess p rho ≤ 1 - X / (2 * ((M : ℝ) - 1)) := by
    unfold mixedOptSuccess
    apply ciSup_le
    intro D
    have h := p53s204_bound p hp rho hrho s D.1 D.2
    rw [← hX] at h
    set u := ∑ j, p j * effectProb (D.1 j) (rho j)
    have hu : 0 ≤ 1 - u := by
      by_contra hc; replace hc := not_le.mp hc
      have : (M : ℝ) * (1 - u) < 0 := mul_neg_of_pos_of_neg (by linarith) hc
      linarith
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hM']
    nlinarith
  linarith

