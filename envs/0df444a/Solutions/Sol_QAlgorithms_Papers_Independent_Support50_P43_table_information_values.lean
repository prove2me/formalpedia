-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P43.table_information_values
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:26:08.799442+00:00
-- url     : https://prove2.me/submissions/a9d28d1c-8490-43b3-aa33-2572a87b572a

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSimpArgs false

section S191P43_gen
open Matrix

variable {ι : Type*} [Fintype ι] {S191P43_inst : DecidableEq ι}

lemma S191P43_cubic (A : Matrix ι ι ℤ) (c : ℝ) (α β : ℤ) (T1 T2 : ℤ) (mα mβ : ℝ)
    (hsym : Aᵀ = A) (hcub : A * A * A - (α + β) • (A * A) + (α * β) • A = 0)
    (ht1 : A.trace = T1) (ht2 : (A * A).trace = T2)
    (hc : 0 < c) (hab : α ≠ β) (ha : 0 < α) (hb : 0 < β)
    (hm1 : mα * α + mβ * β = T1) (hm2 : mα * α ^ 2 + mβ * β ^ 2 = T2) :
    QAlgorithms.vnEntropy ((c : ℂ) • A.map (Int.cast : ℤ → ℂ)) =
      -(mα * (c * α) * Real.logb 2 (c * α) + mβ * (c * β) * Real.logb 2 (c * β)) := by
  set B : Matrix ι ι ℂ := (Int.castRingHom ℂ).mapMatrix A with hB
  have hBdef : A.map (Int.cast : ℤ → ℂ) = B := rfl
  set ρ : Matrix ι ι ℂ := (c : ℂ) • B with hρ
  have hρr : ρ = c • B := by rw [hρ, ← Complex.coe_smul]
  have hsa : IsSelfAdjoint ρ := by
    rw [hρr]
    refine IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) ?_
    show Bᴴ = B
    ext i j
    have := congrFun (congrFun hsym j) i
    simp [hB, conjTranspose_apply, transpose_apply] at this ⊢
    rw [this]
  have hBc : B * B * B - ((α + β : ℤ) : ℝ) • (B * B) + ((α * β : ℤ) : ℝ) • B = 0 := by
    have := congrArg (Int.castRingHom ℂ).mapMatrix hcub
    simp only [map_sub, map_add, map_mul, map_zsmul, map_zero] at this
    rw [← this, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  set a : ℝ := c * α
  set b : ℝ := c * β
  have hapos : 0 < a := mul_pos hc (by exact_mod_cast ha)
  have hbpos : 0 < b := mul_pos hc (by exact_mod_cast hb)
  have hab' : a ≠ b := by
    intro h; apply hab; have := mul_left_cancel₀ hc.ne' h; exact_mod_cast this
  set p : Polynomial ℝ := Polynomial.X ^ 3 - Polynomial.C (a + b) * Polynomial.X ^ 2
    + Polynomial.C (a * b) * Polynomial.X with hp
  have hρc : Polynomial.aeval ρ p = 0 := by
    simp only [hp, map_add, map_sub, map_mul, Polynomial.aeval_X_pow, Polynomial.aeval_C,
      Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [hρr, smul_pow, smul_pow]
    simp only [pow_succ, pow_zero, one_mul]
    push_cast at hBc
    simp only [← add_smul, smul_mul_assoc, one_mul, smul_smul]
    simp only [a, b]
    linear_combination (norm := module) c ^ 3 • hBc
  have hspec : ∀ x ∈ spectrum ℝ ρ, x = 0 ∨ x = a ∨ x = b := by
    intro x hx
    have hmem := spectrum.subset_polynomial_aeval ρ p ⟨x, hx, rfl⟩
    rw [hρc] at hmem
    have hev : p.eval x = 0 := by
      by_contra hne
      apply spectrum.notMem_iff.mpr _ hmem
      simpa using (IsUnit.mk0 _ hne).map (algebraMap ℝ (Matrix ι ι ℂ))
    have : x * (x - a) * (x - b) = 0 := by
      rw [← hev]; simp only [hp, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]; ring
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  set v : ℝ := (Real.logb 2 b - Real.logb 2 a) / (b - a)
  set u : ℝ := Real.logb 2 a - v * a
  have hua : u + v * a = Real.logb 2 a := by simp [u]
  have hub : u + v * b = Real.logb 2 b := by
    simp only [u, v]; field_simp [sub_ne_zero.mpr hab'.symm]; ring
  have hcfc : cfc (fun x : ℝ => x * Real.logb 2 x) ρ = cfc (fun x : ℝ => u * x + v * x ^ 2) ρ := by
    apply cfc_congr
    intro x hx
    rcases hspec x hx with h | h | h <;> subst h
    · simp
    · simp only; rw [← hua]; ring
    · simp only; rw [← hub]; ring
  have hg : cfc (fun x : ℝ => u * x + v * x ^ 2) ρ = u • ρ + v • (ρ * ρ) := by
    rw [cfc_add (a := ρ) (f := fun x : ℝ => u * x) (g := fun x : ℝ => v * x ^ 2),
      cfc_const_mul (a := ρ) u (fun x : ℝ => x), cfc_const_mul (a := ρ) v (fun x : ℝ => x ^ 2),
      cfc_pow (a := ρ) (fun x : ℝ => x) 2, cfc_id' ℝ ρ, pow_two]
  unfold QAlgorithms.vnEntropy
  rw [hBdef, hcfc, hg]
  have htrB : B.trace = (T1 : ℂ) := by
    rw [← ht1, hB, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]; rfl
  have htrBB : (B * B).trace = (T2 : ℂ) := by
    rw [← ht2, hB, ← map_mul, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]; rfl
  rw [hρr, trace_add, trace_smul, trace_smul, smul_mul_smul_comm, trace_smul, trace_smul,
    htrB, htrBB]
  simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero, zero_mul]
  rw [← hm1, ← hm2, ← hua, ← hub]
  simp only [a, b]; ring

end S191P43_gen

section S191P43_marg
open QAlgorithms.Papers.Independent.Claimed50.P33 QAlgorithms.Papers.Independent.Support50.P43

def S191P43_merge {n d : ℕ} (s : Finset (Fin n)) (x : Fin n → Fin d)
    (b : SubBasis (fun _ : Fin n => Fin d) s) : Fin n → Fin d :=
  fun i => if h : i ∈ s then b ⟨i, h⟩ else x i

def S191P43_M {n d : ℕ} (q : (Fin n → Fin d) → ℤ) (s : Finset (Fin n)) :
    Matrix (SubBasis (fun _ : Fin n => Fin d) s × Unit)
      (SubBasis (fun _ : Fin n => Fin d) s × Unit) ℤ :=
  fun a b => ∑ x : Fin n → Fin d,
    if (∀ i (h : i ∈ s), x i = a.1 ⟨i, h⟩) then q x * q (S191P43_merge s x b.1) else 0

lemma S191P43_G1 {n d : ℕ} (ψ : EuclideanSpace ℂ (HomBasis n d)) (c : ℝ)
    (q : (Fin n → Fin d) → ℤ) (hψ : ∀ x, ψ x = (c : ℂ) * (q x : ℂ)) (s : Finset (Fin n)) :
    registerMarginal (trivialExtension (QAlgorithms.pureDensity ψ)) s =
      ((c ^ 2 : ℝ) : ℂ) • (S191P43_M q s).map (Int.cast : ℤ → ℂ) := by
  ext a b
  simp only [registerMarginal, Matrix.smul_apply, Matrix.map_apply, S191P43_M, Int.cast_sum,
    Finset.mul_sum, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (S191P43_merge s x b.1)]
  · by_cases hx : ∀ i (h : i ∈ s), x i = a.1 ⟨i, h⟩
    · rw [if_pos ⟨fun i hi => ⟨hx i hi, by simp [S191P43_merge, hi]⟩,
        fun i hi => by simp [S191P43_merge, hi]⟩, if_pos hx]
      simp only [trivialExtension, QAlgorithms.pureDensity, Matrix.of_apply, hψ, map_mul,
        Complex.conj_ofReal, map_intCast]
      push_cast; ring
    · rw [if_neg (fun h => hx fun i hi => (h.1 i hi).1), if_neg hx]; simp
  · intro y _ hy
    rw [if_neg]
    intro h; apply hy; funext i
    by_cases hi : i ∈ s
    · simp [S191P43_merge, hi, (h.1 i hi).2]
    · simp [S191P43_merge, hi, h.2 i hi]
  · simp

lemma S191P43_ent {n d : ℕ} (ψ : EuclideanSpace ℂ (HomBasis n d)) (c : ℝ)
    (q : (Fin n → Fin d) → ℤ) (hψ : ∀ x, ψ x = (c : ℂ) * (q x : ℂ)) (s : Finset (Fin n))
    (c2 : ℝ) (hc2 : c ^ 2 = c2) (α β T1 T2 : ℤ) (mα mβ la lb : ℝ)
    (hsym : (S191P43_M q s)ᵀ = S191P43_M q s)
    (hcub : S191P43_M q s * S191P43_M q s * S191P43_M q s
      - (α + β) • (S191P43_M q s * S191P43_M q s) + (α * β) • S191P43_M q s = 0)
    (ht1 : (S191P43_M q s).trace = T1) (ht2 : (S191P43_M q s * S191P43_M q s).trace = T2)
    (hc : c ≠ 0) (hab : α ≠ β) (ha : 0 < α) (hb : 0 < β)
    (hm1 : mα * α + mβ * β = T1) (hm2 : mα * α ^ 2 + mβ * β ^ 2 = T2)
    (hla : c2 * α = la) (hlb : c2 * β = lb) :
    marginalEntropyBits (QAlgorithms.pureDensity ψ) s =
      -(mα * la * Real.logb 2 la + mβ * lb * Real.logb 2 lb) := by
  unfold marginalEntropyBits entropyAt
  rw [S191P43_G1 ψ c q hψ s, ← hla, ← hlb, ← hc2]
  exact S191P43_cubic _ _ α β T1 T2 mα mβ hsym hcub ht1 ht2 (by positivity) hab ha hb hm1 hm2

lemma S191P43_entq {n d : ℕ} (ψ : EuclideanSpace ℂ (HomBasis n d)) (c : ℝ)
    (q : (Fin n → Fin d) → ℤ) (hψ : ∀ x, ψ x = (c : ℂ) * (q x : ℂ)) (s : Finset (Fin n))
    (c2 : ℝ) (hc2 : c ^ 2 = c2) (α T1 : ℤ) (la : ℝ)
    (hsym : (S191P43_M q s)ᵀ = S191P43_M q s)
    (hq : S191P43_M q s * S191P43_M q s = α • S191P43_M q s)
    (ht1 : (S191P43_M q s).trace = T1) (hc : c ≠ 0) (ha : 0 < α) (hla : c2 * α = la) :
    marginalEntropyBits (QAlgorithms.pureDensity ψ) s = -((c2 * T1) * Real.logb 2 la) := by
  have hα : (α : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [S191P43_ent ψ c q hψ s c2 hc2 α (α + 1) T1 (α * T1) (T1 / α) 0 la (c2 * (α + 1 : ℤ))
    hsym ?_ ht1 ?_ hc (by omega) ha (by omega) ?_ ?_ hla rfl]
  · rw [← hla]; field_simp; ring
  · rw [hq, Matrix.smul_mul, hq, smul_smul]; module
  · rw [hq, Matrix.trace_smul, ht1, smul_eq_mul]
  · field_simp; simp
  · push_cast; field_simp; ring

lemma S191P43_symm {n d : ℕ} (q : (Fin n → Fin d) → ℤ) (s : Finset (Fin n)) :
    (S191P43_M q s)ᵀ = S191P43_M q s := by
  ext a b
  simp only [Matrix.transpose_apply, S191P43_M]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun x => S191P43_merge s x a.1) (fun x => S191P43_merge s x b.1)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro i h; simp [S191P43_merge, h]
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro i h; simp [S191P43_merge, h]
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    funext i; by_cases h : i ∈ s
    · simp [S191P43_merge, h, hx i h]
    · simp [S191P43_merge, h]
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    funext i; by_cases h : i ∈ s
    · simp [S191P43_merge, h, hx i h]
    · simp [S191P43_merge, h]
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have : S191P43_merge s (S191P43_merge s x a.1) b.1 = x := by
      funext i; by_cases h : i ∈ s
      · simp [S191P43_merge, h, hx i h]
      · simp [S191P43_merge, h]
    rw [this, mul_comm]

lemma S191P43_full {n d : ℕ} (q : (Fin n → Fin d) → ℤ) (s : Finset (Fin n))
    (hs : ∀ i, i ∈ s) (T : ℤ) (ht : (S191P43_M q s).trace = T) :
    S191P43_M q s * S191P43_M q s = T • S191P43_M q s := by
  set v : SubBasis (fun _ : Fin n => Fin d) s × Unit → ℤ :=
    fun a => q (fun i => a.1 ⟨i, hs i⟩) with hv
  have hM : ∀ a b, S191P43_M q s a b = v a * v b := by
    intro a b
    simp only [S191P43_M]
    rw [Finset.sum_eq_single (fun i => a.1 ⟨i, hs i⟩)]
    · rw [if_pos (fun i h => rfl)]
      congr 1
      congr 1; funext i; simp [S191P43_merge, hs i]
    · intro x _ hx
      rw [if_neg]; intro h; apply hx; funext i; exact h i (hs i)
    · simp
  have htr : (S191P43_M q s).trace = ∑ k, v k * v k := by
    simp only [Matrix.trace, Matrix.diag, hM]
  ext a b
  simp only [Matrix.mul_apply, Matrix.smul_apply, hM, smul_eq_mul, ← ht, htr, Finset.sum_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _; ring

lemma S191P43_sub_eq {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix ι ι ℤ)
    (E : Matrix (Fin m) (Fin m) ℤ) (e : ι → Fin m) (hA : ∀ a b, A a b = E (e a) (e b)) :
    A = E.submatrix e e := by
  ext a b; exact hA a b

lemma S191P43_transfer {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix ι ι ℤ)
    (E : Matrix (Fin m) (Fin m) ℤ) (e : ι → Fin m) (he : Function.Bijective e)
    (hA : A = E.submatrix e e) (α β T1 T2 : ℤ)
    (hcub : E * E * E - (α + β) • (E * E) + (α * β) • E = 0)
    (ht1 : E.trace = T1) (ht2 : (E * E).trace = T2) :
    (A * A * A - (α + β) • (A * A) + (α * β) • A = 0) ∧ A.trace = T1 ∧
      (A * A).trace = T2 := by
  rw [hA]
  have hm : ∀ X Y : Matrix (Fin m) (Fin m) ℤ, X.submatrix e e * Y.submatrix e e =
      (X * Y).submatrix e e := fun X Y => (Matrix.submatrix_mul X Y e e e he).symm
  have htr : ∀ X : Matrix (Fin m) (Fin m) ℤ, (X.submatrix e e).trace = X.trace := by
    intro X; simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact he.sum_comp (fun j => X j j)
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, hm]
    ext a b
    have := congrFun (congrFun hcub (e a)) (e b)
    simpa only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply,
      Matrix.zero_apply] using this
  · rw [htr, ht1]
  · rw [hm, htr, ht2]

lemma S191P43_transferq {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix ι ι ℤ)
    (E : Matrix (Fin m) (Fin m) ℤ) (e : ι → Fin m) (he : Function.Bijective e)
    (hA : A = E.submatrix e e) (α T1 : ℤ)
    (hq : E * E = α • E) (ht1 : E.trace = T1) :
    A * A = α • A ∧ A.trace = T1 := by
  rw [hA]
  refine ⟨?_, ?_⟩
  · rw [← Matrix.submatrix_mul E E e e e he, hq]; rfl
  · simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    rw [he.sum_comp (fun j => E j j)]; exact ht1

def S191P43_enc {n d : ℕ} (m : ℕ) [NeZero m] (s : Finset (Fin n)) :
    SubBasis (fun _ : Fin n => Fin d) s × Unit → Fin m := fun a =>
  Fin.ofNat m (∑ i : {i // i ∈ s}, (a.1 i).val * d ^ (s.filter (· < i.val)).card)

lemma S191P43_entE {n d : ℕ} (ψ : EuclideanSpace ℂ (HomBasis n d)) (c : ℝ)
    (q : (Fin n → Fin d) → ℤ) (hψ : ∀ x, ψ x = (c : ℂ) * (q x : ℂ)) (s : Finset (Fin n))
    (c2 : ℝ) (hc2 : c ^ 2 = c2) (m : ℕ) [NeZero m] (E : Matrix (Fin m) (Fin m) ℤ)
    (hE : S191P43_M q s = E.submatrix (S191P43_enc m s) (S191P43_enc m s))
    (hbij : Function.Bijective (S191P43_enc (d := d) m s))
    (α β T1 T2 : ℤ) (mα mβ la lb : ℝ)
    (hcub : E * E * E - (α + β) • (E * E) + (α * β) • E = 0)
    (ht1 : E.trace = T1) (ht2 : (E * E).trace = T2)
    (hc : c ≠ 0) (hab : α ≠ β) (ha : 0 < α) (hb : 0 < β)
    (hm1 : mα * α + mβ * β = T1) (hm2 : mα * α ^ 2 + mβ * β ^ 2 = T2)
    (hla : c2 * α = la) (hlb : c2 * β = lb) :
    marginalEntropyBits (QAlgorithms.pureDensity ψ) s =
      -(mα * la * Real.logb 2 la + mβ * lb * Real.logb 2 lb) := by
  obtain ⟨h1, h2, h3⟩ := S191P43_transfer _ E _ hbij hE α β T1 T2 hcub ht1 ht2
  exact S191P43_ent ψ c q hψ s c2 hc2 α β T1 T2 mα mβ la lb (S191P43_symm _ _) h1 h2 h3 hc hab ha hb
    hm1 hm2 hla hlb

lemma S191P43_entqE {n d : ℕ} (ψ : EuclideanSpace ℂ (HomBasis n d)) (c : ℝ)
    (q : (Fin n → Fin d) → ℤ) (hψ : ∀ x, ψ x = (c : ℂ) * (q x : ℂ)) (s : Finset (Fin n))
    (c2 : ℝ) (hc2 : c ^ 2 = c2) (m : ℕ) [NeZero m] (E : Matrix (Fin m) (Fin m) ℤ)
    (hE : S191P43_M q s = E.submatrix (S191P43_enc m s) (S191P43_enc m s))
    (hbij : Function.Bijective (S191P43_enc (d := d) m s))
    (α T1 : ℤ) (la : ℝ) (hq : E * E = α • E) (ht1 : E.trace = T1)
    (hc : c ≠ 0) (ha : 0 < α) (hla : c2 * α = la) :
    marginalEntropyBits (QAlgorithms.pureDensity ψ) s = -((c2 * T1) * Real.logb 2 la) := by
  obtain ⟨h1, h2⟩ := S191P43_transferq _ E _ hbij hE α T1 hq ht1
  exact S191P43_entq ψ c q hψ s c2 hc2 α T1 la (S191P43_symm _ _) h1 h2 hc ha hla

end S191P43_marg

section S191P43_states
open QAlgorithms.Papers.Independent.Claimed50.P33 QAlgorithms.Papers.Independent.Support50.P43
open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet)

def S191P43_qghz (n : ℕ) : (Fin n → Fin 2) → ℤ := fun x =>
  (if x = fun _ => 0 then 1 else 0) + (if x = fun _ => 1 then 1 else 0)

lemma S191P43_hghz (n : ℕ) (x : Fin n → Fin 2) :
    (ghzKet n true) x = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((S191P43_qghz n x : ℤ) : ℂ) := by
  simp only [ghzKet, QAlgorithms.Papers.Independent.Information100.P21.constantKet, QAlgorithms.ket,
    S191P43_qghz]
  simp [PiLp.single_apply]
  rw [mul_add]; congr 1 <;> split_ifs <;> simp

def S191P43_qdicke (n r : ℕ) : (Fin n → Fin 2) → ℤ := fun x =>
  if (Finset.univ.filter fun i => x i = 1).card = r then 1 else 0

lemma S191P43_hdicke (n r : ℕ) (x : Fin n → Fin 2) :
    (dickeQubitVector n r) x =
      (((Real.sqrt (Nat.choose n r : ℝ))⁻¹ : ℝ) : ℂ) * ((S191P43_qdicke n r x : ℤ) : ℂ) := by
  simp only [dickeQubitVector, QAlgorithms.Papers.Independent.Information100.P22.dicke,
    QAlgorithms.hammingWeight, S191P43_qdicke, Fintype.card_fin]
  simp only [beq_iff_eq]
  split_ifs <;> simp

def S191P43_qanti : (Fin 3 → Fin 3) → ℤ := fun x =>
  if x = ![0,1,2] ∨ x = ![1,2,0] ∨ x = ![2,0,1] then 1
  else if x = ![0,2,1] ∨ x = ![1,0,2] ∨ x = ![2,1,0] then -1 else 0

lemma S191P43_hanti (x : Fin 3 → Fin 3) :
    antisymmetric x = (((Real.sqrt 6)⁻¹ : ℝ) : ℂ) * ((S191P43_qanti x : ℤ) : ℂ) := by
  simp only [antisymmetric, S191P43_qanti, PiLp.toLp_apply]
  split_ifs <;> simp

def S191P43_qcl : (Fin 4 → Fin 2) → ℤ := fun x =>
  if x = ![0,0,0,0] ∨ x = ![0,0,1,1] ∨ x = ![1,1,0,0] then 1
  else if x = ![1,1,1,1] then -1 else 0

lemma S191P43_hcl (x : Fin 4 → Fin 2) :
    cluster x = (((1:ℝ)/2 : ℝ) : ℂ) * ((S191P43_qcl x : ℤ) : ℂ) := by
  simp only [cluster, S191P43_qcl, PiLp.toLp_apply]
  split_ifs <;> simp

lemma S191P43_L2 : Real.logb 2 (1/2 : ℝ) = -1 := by
  rw [one_div, Real.logb_inv, Real.logb_self_eq_one one_lt_two]
lemma S191P43_L4 : Real.logb 2 (1/4 : ℝ) = -2 := by
  rw [one_div, Real.logb_inv, show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two]; ring
lemma S191P43_L1 : Real.logb 2 (1 : ℝ) = 0 := Real.logb_one
lemma S191P43_L13 : Real.logb 2 (1/3 : ℝ) = -Real.logb 2 3 := by
  rw [one_div, Real.logb_inv]
lemma S191P43_L23 : Real.logb 2 (2/3 : ℝ) = 1 - Real.logb 2 3 := by
  rw [Real.logb_div (by norm_num) (by norm_num), Real.logb_self_eq_one one_lt_two]
lemma S191P43_L34 : Real.logb 2 (3/4 : ℝ) = Real.logb 2 3 - 2 := by
  rw [Real.logb_div (by norm_num) (by norm_num), show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two]; ring
lemma S191P43_L16 : Real.logb 2 (1/6 : ℝ) = -1 - Real.logb 2 3 := by
  rw [one_div, Real.logb_inv, show (6:ℝ) = 2 * 3 by norm_num, Real.logb_mul (by norm_num) (by norm_num),
    Real.logb_self_eq_one one_lt_two]; ring
lemma S191P43_L19 : Real.logb 2 (1/9 : ℝ) = -2 * Real.logb 2 3 := by
  rw [one_div, Real.logb_inv, show (9:ℝ) = 3 ^ (2:ℕ) by norm_num, Real.logb_pow]; ring

lemma S191P43_h13 : QAlgorithms.binEntropy2 (1/3) = Real.logb 2 3 - 2/3 := by
  unfold QAlgorithms.binEntropy2 Real.binEntropy
  rw [show (1:ℝ) - 1/3 = 2/3 by norm_num, show ((1:ℝ)/3)⁻¹ = 3 by norm_num,
    show ((2:ℝ)/3)⁻¹ = 3/2 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.logb]
  field_simp; ring

lemma S191P43_h14 : QAlgorithms.binEntropy2 (1/4) = 2 - 3/4 * Real.logb 2 3 := by
  unfold QAlgorithms.binEntropy2 Real.binEntropy
  rw [show (1:ℝ) - 1/4 = 3/4 by norm_num, show ((1:ℝ)/4)⁻¹ = 2^2 by norm_num,
    show ((3:ℝ)/4)⁻¹ = 2^2/3 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow,
    Real.logb]
  field_simp; ring

lemma S191P43_common2 {D : Fin 2 → Type} [∀ i, Fintype (D i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    commonOn ρ Finset.univ = marginalEntropyBits ρ {0} + marginalEntropyBits ρ {1} - marginalEntropyBits ρ {0, 1} := by
  unfold commonOn
  rw [Finset.sum_filter, show (Finset.univ : Finset (Fin 2)) = insert 0 (insert 1 (∅)) by decide]
  simp (config := {decide := true}) only [Finset.sum_powerset_insert, Finset.mem_insert,
    Finset.notMem_empty, Finset.powerset_empty, Finset.sum_singleton]
  simp
  ring

lemma S191P43_alt2 {D : Fin 2 → Type} [∀ i, Fintype (D i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    alternativeOn ρ Finset.univ = marginalEntropyBits ρ {1} + marginalEntropyBits ρ {0} - 1 * marginalEntropyBits ρ {0, 1} := by
  unfold alternativeOn
  have e : ∀ (i : Fin 2) (inst : DecidableEq (Fin 2)),
      @Finset.erase _ inst Finset.univ i = Finset.univ.filter (· ≠ i) := by
    intro i inst; ext x; simp [and_comm]
  simp only [e, Fin.sum_univ_two, Finset.card_univ, Fintype.card_fin]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp [Finset.filter_insert, Finset.filter_singleton]
  try norm_num

lemma S191P43_common3 {D : Fin 3 → Type} [∀ i, Fintype (D i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    commonOn ρ Finset.univ = marginalEntropyBits ρ {0} + marginalEntropyBits ρ {1} + marginalEntropyBits ρ {2} - marginalEntropyBits ρ {0, 1} - marginalEntropyBits ρ {0, 2} - marginalEntropyBits ρ {1, 2} + marginalEntropyBits ρ {0, 1, 2} := by
  unfold commonOn
  rw [Finset.sum_filter, show (Finset.univ : Finset (Fin 3)) = insert 0 (insert 1 (insert 2 (∅))) by decide]
  simp (config := {decide := true}) only [Finset.sum_powerset_insert, Finset.mem_insert,
    Finset.notMem_empty, Finset.powerset_empty, Finset.sum_singleton]
  simp
  ring

lemma S191P43_alt3 {D : Fin 3 → Type} [∀ i, Fintype (D i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    alternativeOn ρ Finset.univ = marginalEntropyBits ρ {1, 2} + marginalEntropyBits ρ {0, 2} + marginalEntropyBits ρ {0, 1} - 2 * marginalEntropyBits ρ {0, 1, 2} := by
  unfold alternativeOn
  have e : ∀ (i : Fin 3) (inst : DecidableEq (Fin 3)),
      @Finset.erase _ inst Finset.univ i = Finset.univ.filter (· ≠ i) := by
    intro i inst; ext x; simp [and_comm]
  simp only [e, Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin]
  rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  simp [Finset.filter_insert, Finset.filter_singleton]
  try norm_num

lemma S191P43_common4 {D : Fin 4 → Type} [∀ i, Fintype (D i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    commonOn ρ Finset.univ = marginalEntropyBits ρ {0} + marginalEntropyBits ρ {1} + marginalEntropyBits ρ {2} + marginalEntropyBits ρ {3} - marginalEntropyBits ρ {0, 1} - marginalEntropyBits ρ {0, 2} - marginalEntropyBits ρ {0, 3} - marginalEntropyBits ρ {1, 2} - marginalEntropyBits ρ {1, 3} - marginalEntropyBits ρ {2, 3} + marginalEntropyBits ρ {0, 1, 2} + marginalEntropyBits ρ {0, 1, 3} + marginalEntropyBits ρ {0, 2, 3} + marginalEntropyBits ρ {1, 2, 3} - marginalEntropyBits ρ {0, 1, 2, 3} := by
  unfold commonOn
  rw [Finset.sum_filter, show (Finset.univ : Finset (Fin 4)) = insert 0 (insert 1 (insert 2 (insert 3 (∅)))) by decide]
  simp (config := {decide := true}) only [Finset.sum_powerset_insert, Finset.mem_insert,
    Finset.notMem_empty, Finset.powerset_empty, Finset.sum_singleton]
  simp
  ring

lemma S191P43_alt4 {D : Fin 4 → Type} [∀ i, Fintype (D i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    alternativeOn ρ Finset.univ = marginalEntropyBits ρ {1, 2, 3} + marginalEntropyBits ρ {0, 2, 3} + marginalEntropyBits ρ {0, 1, 3} + marginalEntropyBits ρ {0, 1, 2} - 3 * marginalEntropyBits ρ {0, 1, 2, 3} := by
  unfold alternativeOn
  have e : ∀ (i : Fin 4) (inst : DecidableEq (Fin 4)),
      @Finset.erase _ inst Finset.univ i = Finset.univ.filter (· ≠ i) := by
    intro i inst; ext x; simp [and_comm]
  simp only [e, Fin.sum_univ_four, Finset.card_univ, Fintype.card_fin]
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  simp [Finset.filter_insert, Finset.filter_singleton]
  try norm_num

set_option maxRecDepth 100000 in
lemma S191P43_pair_ghz2 : informationPair (ghzKet 2 true) = (2, 2) := by
  unfold informationPair
  rw [S191P43_common2, S191P43_alt2]
  have h0 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 2 true)) ({0} : Finset (Fin 2)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 2 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 2) (S191P43_hghz 2) ({0} : Finset (Fin 2)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h1 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 2 true)) ({1} : Finset (Fin 2)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 2 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 2) (S191P43_hghz 2) ({1} : Finset (Fin 2)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h2 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 2 true)) ({0, 1} : Finset (Fin 2)) = (0 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entq (ghzKet 2 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 2) (S191P43_hghz 2) ({0, 1} : Finset (Fin 2)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 2 (1 : ℝ) (S191P43_symm _ _) (S191P43_full _ _ (by decide) 2 (by decide +kernel)) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L1]
    ring
  rw [h0, h1, h2]
  simp only [S191P43_h13, S191P43_h14, Prod.mk.injEq]
  constructor <;> ring

set_option maxRecDepth 100000 in
lemma S191P43_pair_ghz3 : informationPair (ghzKet 3 true) = (0, 3) := by
  unfold informationPair
  rw [S191P43_common3, S191P43_alt3]
  have h0 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 3 true)) ({0} : Finset (Fin 3)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 3 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 3) (S191P43_hghz 3) ({0} : Finset (Fin 3)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h1 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 3 true)) ({1} : Finset (Fin 3)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 3 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 3) (S191P43_hghz 3) ({1} : Finset (Fin 3)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h2 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 3 true)) ({2} : Finset (Fin 3)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 3 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 3) (S191P43_hghz 3) ({2} : Finset (Fin 3)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h3 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 3 true)) ({0, 1} : Finset (Fin 3)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 3 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 3) (S191P43_hghz 3) ({0, 1} : Finset (Fin 3)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 4 (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h4 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 3 true)) ({0, 2} : Finset (Fin 3)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 3 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 3) (S191P43_hghz 3) ({0, 2} : Finset (Fin 3)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 4 (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h5 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 3 true)) ({1, 2} : Finset (Fin 3)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 3 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 3) (S191P43_hghz 3) ({1, 2} : Finset (Fin 3)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 4 (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h6 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 3 true)) ({0, 1, 2} : Finset (Fin 3)) = (0 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entq (ghzKet 3 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 3) (S191P43_hghz 3) ({0, 1, 2} : Finset (Fin 3)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 2 (1 : ℝ) (S191P43_symm _ _) (S191P43_full _ _ (by decide) 2 (by decide +kernel)) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L1]
    ring
  rw [h0, h1, h2, h3, h4, h5, h6]
  simp only [S191P43_h13, S191P43_h14, Prod.mk.injEq]
  constructor <;> ring

set_option maxRecDepth 100000 in
lemma S191P43_pair_w3 : informationPair (dickeQubitVector 3 1) = (0, 3 * QAlgorithms.binEntropy2 (1/3)) := by
  unfold informationPair
  rw [S191P43_common3, S191P43_alt3]
  have h0 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 3 1)) ({0} : Finset (Fin 3)) = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 3 1) ((Real.sqrt (Nat.choose 3 1 : ℝ))⁻¹) (S191P43_qdicke 3 1) (S191P43_hdicke 3 1) ({0} : Finset (Fin 3)) (1/3 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 2 (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 3 5 (1 : ℝ) (1 : ℝ) (1/3 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L13, S191P43_L23]
    ring
  have h1 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 3 1)) ({1} : Finset (Fin 3)) = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 3 1) ((Real.sqrt (Nat.choose 3 1 : ℝ))⁻¹) (S191P43_qdicke 3 1) (S191P43_hdicke 3 1) ({1} : Finset (Fin 3)) (1/3 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 2 (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 3 5 (1 : ℝ) (1 : ℝ) (1/3 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L13, S191P43_L23]
    ring
  have h2 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 3 1)) ({2} : Finset (Fin 3)) = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 3 1) ((Real.sqrt (Nat.choose 3 1 : ℝ))⁻¹) (S191P43_qdicke 3 1) (S191P43_hdicke 3 1) ({2} : Finset (Fin 3)) (1/3 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 2 (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 3 5 (1 : ℝ) (1 : ℝ) (1/3 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L13, S191P43_L23]
    ring
  have h3 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 3 1)) ({0, 1} : Finset (Fin 3)) = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 3 1) ((Real.sqrt (Nat.choose 3 1 : ℝ))⁻¹) (S191P43_qdicke 3 1) (S191P43_hdicke 3 1) ({0, 1} : Finset (Fin 3)) (1/3 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 1, 0; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 3 5 (1 : ℝ) (1 : ℝ) (1/3 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L13, S191P43_L23]
    ring
  have h4 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 3 1)) ({0, 2} : Finset (Fin 3)) = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 3 1) ((Real.sqrt (Nat.choose 3 1 : ℝ))⁻¹) (S191P43_qdicke 3 1) (S191P43_hdicke 3 1) ({0, 2} : Finset (Fin 3)) (1/3 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 1, 0; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 3 5 (1 : ℝ) (1 : ℝ) (1/3 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L13, S191P43_L23]
    ring
  have h5 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 3 1)) ({1, 2} : Finset (Fin 3)) = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 3 1) ((Real.sqrt (Nat.choose 3 1 : ℝ))⁻¹) (S191P43_qdicke 3 1) (S191P43_hdicke 3 1) ({1, 2} : Finset (Fin 3)) (1/3 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 1, 0; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 3 5 (1 : ℝ) (1 : ℝ) (1/3 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L13, S191P43_L23]
    ring
  have h6 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 3 1)) ({0, 1, 2} : Finset (Fin 3)) = (0 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entq (dickeQubitVector 3 1) ((Real.sqrt (Nat.choose 3 1 : ℝ))⁻¹) (S191P43_qdicke 3 1) (S191P43_hdicke 3 1) ({0, 1, 2} : Finset (Fin 3)) (1/3 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 3 3 (1 : ℝ) (S191P43_symm _ _) (S191P43_full _ _ (by decide) 3 (by decide +kernel)) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L1]
    ring
  rw [h0, h1, h2, h3, h4, h5, h6]
  simp only [S191P43_h13, S191P43_h14, Prod.mk.injEq]
  constructor <;> ring

set_option maxRecDepth 100000 in
lemma S191P43_pair_anti : informationPair antisymmetric = (0, 3 * Real.logb 2 3) := by
  unfold informationPair
  rw [S191P43_common3, S191P43_alt3]
  have h0 : marginalEntropyBits (QAlgorithms.pureDensity antisymmetric) ({0} : Finset (Fin 3)) = (0 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE antisymmetric ((Real.sqrt 6)⁻¹) S191P43_qanti S191P43_hanti ({0} : Finset (Fin 3)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 3 (!![2, 0, 0; 0, 2, 0; 0, 0, 2] : Matrix (Fin 3) (Fin 3) ℤ) (by decide +kernel) (by decide +kernel) 2 6 (1/3 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L13]
    ring
  have h1 : marginalEntropyBits (QAlgorithms.pureDensity antisymmetric) ({1} : Finset (Fin 3)) = (0 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE antisymmetric ((Real.sqrt 6)⁻¹) S191P43_qanti S191P43_hanti ({1} : Finset (Fin 3)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 3 (!![2, 0, 0; 0, 2, 0; 0, 0, 2] : Matrix (Fin 3) (Fin 3) ℤ) (by decide +kernel) (by decide +kernel) 2 6 (1/3 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L13]
    ring
  have h2 : marginalEntropyBits (QAlgorithms.pureDensity antisymmetric) ({2} : Finset (Fin 3)) = (0 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE antisymmetric ((Real.sqrt 6)⁻¹) S191P43_qanti S191P43_hanti ({2} : Finset (Fin 3)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 3 (!![2, 0, 0; 0, 2, 0; 0, 0, 2] : Matrix (Fin 3) (Fin 3) ℤ) (by decide +kernel) (by decide +kernel) 2 6 (1/3 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L13]
    ring
  have h3 : marginalEntropyBits (QAlgorithms.pureDensity antisymmetric) ({0, 1} : Finset (Fin 3)) = (0 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE antisymmetric ((Real.sqrt 6)⁻¹) S191P43_qanti S191P43_hanti ({0, 1} : Finset (Fin 3)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 9 (!![0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 0, 0; 0, -1, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, -1, 0; 0, 0, -1, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, -1, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 9) (Fin 9) ℤ) (by decide +kernel) (by decide +kernel) 2 6 (1/3 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L13]
    ring
  have h4 : marginalEntropyBits (QAlgorithms.pureDensity antisymmetric) ({0, 2} : Finset (Fin 3)) = (0 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE antisymmetric ((Real.sqrt 6)⁻¹) S191P43_qanti S191P43_hanti ({0, 2} : Finset (Fin 3)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 9 (!![0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 0, 0; 0, -1, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, -1, 0; 0, 0, -1, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, -1, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 9) (Fin 9) ℤ) (by decide +kernel) (by decide +kernel) 2 6 (1/3 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L13]
    ring
  have h5 : marginalEntropyBits (QAlgorithms.pureDensity antisymmetric) ({1, 2} : Finset (Fin 3)) = (0 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE antisymmetric ((Real.sqrt 6)⁻¹) S191P43_qanti S191P43_hanti ({1, 2} : Finset (Fin 3)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 9 (!![0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 0, 0; 0, -1, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, -1, 0; 0, 0, -1, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, -1, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 9) (Fin 9) ℤ) (by decide +kernel) (by decide +kernel) 2 6 (1/3 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L13]
    ring
  have h6 : marginalEntropyBits (QAlgorithms.pureDensity antisymmetric) ({0, 1, 2} : Finset (Fin 3)) = (0 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entq antisymmetric ((Real.sqrt 6)⁻¹) S191P43_qanti S191P43_hanti ({0, 1, 2} : Finset (Fin 3)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 6 6 (1 : ℝ) (S191P43_symm _ _) (S191P43_full _ _ (by decide) 6 (by decide +kernel)) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L1]
    ring
  rw [h0, h1, h2, h3, h4, h5, h6]
  simp only [S191P43_h13, S191P43_h14, Prod.mk.injEq]
  constructor <;> ring

set_option maxRecDepth 100000 in
lemma S191P43_pair_ghz4 : informationPair (ghzKet 4 true) = (2, 4) := by
  unfold informationPair
  rw [S191P43_common4, S191P43_alt4]
  have h0 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({0} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({0} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h1 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({1} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({1} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h2 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({2} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({2} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h3 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({3} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h4 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({0, 1} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({0, 1} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 4 (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h5 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({0, 2} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({0, 2} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 4 (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h6 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({0, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({0, 3} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 4 (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h7 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({1, 2} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({1, 2} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 4 (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h8 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({1, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({1, 3} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 4 (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h9 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({2, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({2, 3} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 4 (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h10 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({0, 1, 2} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({0, 1, 2} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 8 (!![1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h11 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({0, 1, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({0, 1, 3} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 8 (!![1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h12 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({0, 2, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({0, 2, 3} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 8 (!![1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h13 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({1, 2, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({1, 2, 3} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 8 (!![1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 1 2 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h14 : marginalEntropyBits (QAlgorithms.pureDensity (ghzKet 4 true)) ({0, 1, 2, 3} : Finset (Fin 4)) = (0 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entq (ghzKet 4 true) ((Real.sqrt 2)⁻¹) (S191P43_qghz 4) (S191P43_hghz 4) ({0, 1, 2, 3} : Finset (Fin 4)) (1/2 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) 2 2 (1 : ℝ) (S191P43_symm _ _) (S191P43_full _ _ (by decide) 2 (by decide +kernel)) (by decide +kernel) (by positivity) (by norm_num) (by norm_num), S191P43_L1]
    ring
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  simp only [S191P43_h13, S191P43_h14, Prod.mk.injEq]
  constructor <;> ring

set_option maxRecDepth 100000 in
lemma S191P43_pair_w4 : informationPair (dickeQubitVector 4 1) = (8 * QAlgorithms.binEntropy2 (1/4) - 6, 4 * QAlgorithms.binEntropy2 (1/4)) := by
  unfold informationPair
  rw [S191P43_common4, S191P43_alt4]
  have h0 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({0} : Finset (Fin 4)) = (2 : ℝ) + (-3/4 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({0} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 2 (!![3, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 3 4 10 (1 : ℝ) (1 : ℝ) (1/4 : ℝ) (3/4 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L4, S191P43_L34]
    ring
  have h1 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({1} : Finset (Fin 4)) = (2 : ℝ) + (-3/4 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({1} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 2 (!![3, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 3 4 10 (1 : ℝ) (1 : ℝ) (1/4 : ℝ) (3/4 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L4, S191P43_L34]
    ring
  have h2 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({2} : Finset (Fin 4)) = (2 : ℝ) + (-3/4 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({2} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 2 (!![3, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 3 4 10 (1 : ℝ) (1 : ℝ) (1/4 : ℝ) (3/4 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L4, S191P43_L34]
    ring
  have h3 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({3} : Finset (Fin 4)) = (2 : ℝ) + (-3/4 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({3} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 2 (!![3, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 1 3 4 10 (1 : ℝ) (1 : ℝ) (1/4 : ℝ) (3/4 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L4, S191P43_L34]
    ring
  have h4 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({0, 1} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({0, 1} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![2, 0, 0, 0; 0, 1, 1, 0; 0, 1, 1, 0; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h5 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({0, 2} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({0, 2} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![2, 0, 0, 0; 0, 1, 1, 0; 0, 1, 1, 0; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h6 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({0, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({0, 3} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![2, 0, 0, 0; 0, 1, 1, 0; 0, 1, 1, 0; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h7 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({1, 2} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({1, 2} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![2, 0, 0, 0; 0, 1, 1, 0; 0, 1, 1, 0; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h8 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({1, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({1, 3} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![2, 0, 0, 0; 0, 1, 1, 0; 0, 1, 1, 0; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h9 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({2, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({2, 3} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![2, 0, 0, 0; 0, 1, 1, 0; 0, 1, 1, 0; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h10 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({0, 1, 2} : Finset (Fin 4)) = (2 : ℝ) + (-3/4 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({0, 1, 2} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 8 (!![1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 1 3 4 10 (1 : ℝ) (1 : ℝ) (1/4 : ℝ) (3/4 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L4, S191P43_L34]
    ring
  have h11 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({0, 1, 3} : Finset (Fin 4)) = (2 : ℝ) + (-3/4 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({0, 1, 3} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 8 (!![1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 1 3 4 10 (1 : ℝ) (1 : ℝ) (1/4 : ℝ) (3/4 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L4, S191P43_L34]
    ring
  have h12 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({0, 2, 3} : Finset (Fin 4)) = (2 : ℝ) + (-3/4 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({0, 2, 3} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 8 (!![1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 1 3 4 10 (1 : ℝ) (1 : ℝ) (1/4 : ℝ) (3/4 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L4, S191P43_L34]
    ring
  have h13 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({1, 2, 3} : Finset (Fin 4)) = (2 : ℝ) + (-3/4 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({1, 2, 3} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 8 (!![1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 1 3 4 10 (1 : ℝ) (1 : ℝ) (1/4 : ℝ) (3/4 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L4, S191P43_L34]
    ring
  have h14 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 1)) ({0, 1, 2, 3} : Finset (Fin 4)) = (0 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entq (dickeQubitVector 4 1) ((Real.sqrt (Nat.choose 4 1 : ℝ))⁻¹) (S191P43_qdicke 4 1) (S191P43_hdicke 4 1) ({0, 1, 2, 3} : Finset (Fin 4)) (1/4 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 4 (1 : ℝ) (S191P43_symm _ _) (S191P43_full _ _ (by decide) 4 (by decide +kernel)) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L1]
    ring
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  simp only [S191P43_h13, S191P43_h14, Prod.mk.injEq]
  constructor <;> ring

set_option maxRecDepth 100000 in
lemma S191P43_pair_d42 : informationPair (dickeQubitVector 4 2) = (8 * QAlgorithms.binEntropy2 (1/4) - 6, 4) := by
  unfold informationPair
  rw [S191P43_common4, S191P43_alt4]
  have h0 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({0} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({0} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 2 (!![3, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 3 6 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h1 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({1} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({1} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 2 (!![3, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 3 6 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h2 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({2} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({2} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 2 (!![3, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 3 6 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h3 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({3} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 2 (!![3, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 3 6 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h4 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({0, 1} : Finset (Fin 4)) = (-1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({0, 1} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![1, 0, 0, 0; 0, 2, 2, 0; 0, 2, 2, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 4 6 18 (2 : ℝ) (1 : ℝ) (1/6 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L16, S191P43_L23]
    ring
  have h5 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({0, 2} : Finset (Fin 4)) = (-1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({0, 2} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![1, 0, 0, 0; 0, 2, 2, 0; 0, 2, 2, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 4 6 18 (2 : ℝ) (1 : ℝ) (1/6 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L16, S191P43_L23]
    ring
  have h6 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({0, 3} : Finset (Fin 4)) = (-1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({0, 3} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![1, 0, 0, 0; 0, 2, 2, 0; 0, 2, 2, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 4 6 18 (2 : ℝ) (1 : ℝ) (1/6 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L16, S191P43_L23]
    ring
  have h7 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({1, 2} : Finset (Fin 4)) = (-1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({1, 2} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![1, 0, 0, 0; 0, 2, 2, 0; 0, 2, 2, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 4 6 18 (2 : ℝ) (1 : ℝ) (1/6 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L16, S191P43_L23]
    ring
  have h8 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({1, 3} : Finset (Fin 4)) = (-1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({1, 3} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![1, 0, 0, 0; 0, 2, 2, 0; 0, 2, 2, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 4 6 18 (2 : ℝ) (1 : ℝ) (1/6 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L16, S191P43_L23]
    ring
  have h9 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({2, 3} : Finset (Fin 4)) = (-1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({2, 3} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 4 (!![1, 0, 0, 0; 0, 2, 2, 0; 0, 2, 2, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 4 6 18 (2 : ℝ) (1 : ℝ) (1/6 : ℝ) (2/3 : ℝ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), S191P43_L16, S191P43_L23]
    ring
  have h10 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({0, 1, 2} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({0, 1, 2} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 8 (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 3 6 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h11 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({0, 1, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({0, 1, 3} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 8 (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 3 6 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h12 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({0, 2, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({0, 2, 3} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 8 (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 3 6 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h13 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({1, 2, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({1, 2, 3} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 8 (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 3 6 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h14 : marginalEntropyBits (QAlgorithms.pureDensity (dickeQubitVector 4 2)) ({0, 1, 2, 3} : Finset (Fin 4)) = (0 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entq (dickeQubitVector 4 2) ((Real.sqrt (Nat.choose 4 2 : ℝ))⁻¹) (S191P43_qdicke 4 2) (S191P43_hdicke 4 2) ({0, 1, 2, 3} : Finset (Fin 4)) (1/6 : ℝ) (by rw [inv_pow, Real.sq_sqrt (by positivity)]; norm_num [Nat.choose]) 6 6 (1 : ℝ) (S191P43_symm _ _) (S191P43_full _ _ (by decide) 6 (by decide +kernel)) (by decide +kernel) (by norm_num [Nat.choose]) (by norm_num) (by norm_num), S191P43_L1]
    ring
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  simp only [S191P43_h13, S191P43_h14, Prod.mk.injEq]
  constructor <;> ring

set_option maxRecDepth 100000 in
lemma S191P43_pair_cl : informationPair cluster = (-2, 4) := by
  unfold informationPair
  rw [S191P43_common4, S191P43_alt4]
  have h0 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({0} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({0} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 2 (!![2, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h1 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({1} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({1} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 2 (!![2, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h2 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({2} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({2} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 2 (!![2, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h3 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({3} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 2 (!![2, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h4 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({0, 1} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({0, 1} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 4 (!![2, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 2] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h5 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({0, 2} : Finset (Fin 4)) = (2 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({0, 2} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 4 (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 4 (1/4 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L4]
    ring
  have h6 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({0, 3} : Finset (Fin 4)) = (2 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({0, 3} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 4 (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 4 (1/4 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L4]
    ring
  have h7 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({1, 2} : Finset (Fin 4)) = (2 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({1, 2} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 4 (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 4 (1/4 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L4]
    ring
  have h8 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({1, 3} : Finset (Fin 4)) = (2 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({1, 3} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 4 (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 1 4 (1/4 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L4]
    ring
  have h9 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({2, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({2, 3} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 4 (!![2, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 2] : Matrix (Fin 4) (Fin 4) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h10 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({0, 1, 2} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({0, 1, 2} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 8 (!![1, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 1] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h11 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({0, 1, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({0, 1, 3} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 8 (!![1, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 1] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h12 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({0, 2, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({0, 2, 3} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 8 (!![1, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 1, 0; 0, -1, 0, 0, 0, 0, 0, 1] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h13 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({1, 2, 3} : Finset (Fin 4)) = (1 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entqE cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({1, 2, 3} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 8 (!![1, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 1, 0; 0, -1, 0, 0, 0, 0, 0, 1] : Matrix (Fin 8) (Fin 8) ℤ) (by decide +kernel) (by decide +kernel) 2 4 (1/2 : ℝ) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L2]
    ring
  have h14 : marginalEntropyBits (QAlgorithms.pureDensity cluster) ({0, 1, 2, 3} : Finset (Fin 4)) = (0 : ℝ) + (0 : ℝ) * Real.logb 2 3 := by
    rw [S191P43_entq cluster ((1:ℝ)/2) S191P43_qcl S191P43_hcl ({0, 1, 2, 3} : Finset (Fin 4)) (1/4 : ℝ) (by norm_num) 4 4 (1 : ℝ) (S191P43_symm _ _) (S191P43_full _ _ (by decide) 4 (by decide +kernel)) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num), S191P43_L1]
    ring
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  simp only [S191P43_h13, S191P43_h14, Prod.mk.injEq]
  constructor <;> ring

end S191P43_states

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis) in
open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet) in
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P43 in
/-- Table I, PDF p.5 (announced on p.3), all eight rows. -/
theorem solution :
    informationPair (ghzKet 2 true) = (2,2) ∧
    informationPair (ghzKet 3 true) = (0,3) ∧
    informationPair (dickeQubitVector 3 1) = (0,3 * binEntropy2 (1/3)) ∧
    informationPair antisymmetric = (0,3 * Real.logb 2 3) ∧
    informationPair (ghzKet 4 true) = (2,4) ∧
    informationPair (dickeQubitVector 4 1) = (8 * binEntropy2 (1/4) - 6,4 * binEntropy2 (1/4)) ∧
    informationPair (dickeQubitVector 4 2) = (8 * binEntropy2 (1/4) - 6,4) ∧
    informationPair cluster = (-2,4) :=
  ⟨S191P43_pair_ghz2, S191P43_pair_ghz3, S191P43_pair_w3, S191P43_pair_anti, S191P43_pair_ghz4,
    S191P43_pair_w4, S191P43_pair_d42, S191P43_pair_cl⟩

#print axioms solution
