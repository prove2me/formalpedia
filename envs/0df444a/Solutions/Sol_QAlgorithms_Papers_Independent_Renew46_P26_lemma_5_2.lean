-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T10:06:32.640649+00:00
-- url     : https://prove2.me/submissions/e31b571a-dbf3-4fa3-a8ae-708d94932d15

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

open scoped BigOperators

namespace X7B17L52
open QAlgorithms.Papers.Independent.Renew46.P26

variable {d : ℕ} {G : Type*} [Fintype G]

def X7_ip (P : G → Module.End ℂ (Fin d → ℂ)) (x y : Fin d → ℂ) : ℂ :=
  ∑ g, ∑ k, star (P g x k) * P g y k

variable (P : G → Module.End ℂ (Fin d → ℂ))

lemma X7_ip_add_left (x x' y : Fin d → ℂ) :
    X7_ip P (x + x') y = X7_ip P x y + X7_ip P x' y := by
  simp [X7_ip, map_add, add_mul, Finset.sum_add_distrib]

lemma X7_ip_add_right (x y y' : Fin d → ℂ) :
    X7_ip P x (y + y') = X7_ip P x y + X7_ip P x y' := by
  simp [X7_ip, map_add, mul_add, Finset.sum_add_distrib]

lemma X7_ip_zero_left (y : Fin d → ℂ) : X7_ip P 0 y = 0 := by
  simp [X7_ip]

lemma X7_ip_zero_right (x : Fin d → ℂ) : X7_ip P x 0 = 0 := by
  simp [X7_ip]

lemma X7_ip_smul_left (c : ℂ) (x y : Fin d → ℂ) :
    X7_ip P (c • x) y = star c * X7_ip P x y := by
  simp only [X7_ip, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul']; ring

lemma X7_ip_smul_right (c : ℂ) (x y : Fin d → ℂ) :
    X7_ip P x (c • y) = c * X7_ip P x y := by
  simp only [X7_ip, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma X7_ip_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin d → ℂ) (y : Fin d → ℂ) :
    X7_ip P (∑ i ∈ s, f i) y = ∑ i ∈ s, X7_ip P (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [X7_ip_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, X7_ip_add_left, ih]

lemma X7_ip_sum_right {ι : Type*} (s : Finset ι) (f : ι → Fin d → ℂ) (x : Fin d → ℂ) :
    X7_ip P x (∑ i ∈ s, f i) = ∑ i ∈ s, X7_ip P x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [X7_ip_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, X7_ip_add_right, ih]

lemma X7_ip_inv {H : Type*} [Group H] [Fintype H] (P : H → Module.End ℂ (Fin d → ℂ))
    (hmul : ∀ g h z, P g (P h z) = P (g * h) z) (h : H) (x y : Fin d → ℂ) :
    X7_ip P (P h x) (P h y) = X7_ip P x y := by
  simp only [X7_ip, hmul]
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => rfl)

lemma X7_ip_self {H : Type*} [Group H] [Fintype H] (P : H → Module.End ℂ (Fin d → ℂ))
    (h1 : P 1 = 1) (x : Fin d → ℂ) (hx : X7_ip P x x = 0) : x = 0 := by
  have hre : ∀ z : ℂ, (star z * z).re = Complex.normSq z := by
    intro z; simp [Complex.normSq_apply]
  have h0 : (X7_ip P x x).re = 0 := by rw [hx]; rfl
  simp only [X7_ip, Complex.re_sum, hre] at h0
  have hnn : ∀ g ∈ (Finset.univ : Finset H), 0 ≤ ∑ k, Complex.normSq (P g x k) :=
    fun g _ => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
  have hg := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 1 (Finset.mem_univ _)
  rw [h1] at hg
  have hk := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => Complex.normSq_nonneg ((1 : Module.End ℂ (Fin d → ℂ)) x k))).1 hg
  funext k
  have := hk k (Finset.mem_univ _)
  simpa using this

lemma X7_key {H : Type*} [Group H] [Fintype H] (P : H → Module.End ℂ (Fin d → ℂ))
    (h1 : P 1 = 1)
    (X X' S : Module.End ℂ (Fin d → ℂ))
    (hXsa : ∀ x y, X7_ip P (X x) y = X7_ip P x (X y))
    (hS : ∀ x y, X7_ip P (S x) (S y) = X7_ip P x y)
    (hrel : S * X' = X * S + 1) (b ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (v : Fin d → ℂ) (hv : v ≠ 0) (hXv : X v = b • v) (hX'v : X' v = (b + ε) • v) :
    S v = ε • v := by
  have hεs : star ε = ε := by rcases hε with rfl | rfl <;> simp
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hvv : X7_ip P v v ≠ 0 := fun h => hv (X7_ip_self P h1 v h)
  have hb : star b = b := by
    have := hXsa v v
    rw [hXv, X7_ip_smul_left, X7_ip_smul_right] at this
    exact mul_right_cancel₀ hvv this
  have hXw : X (S v) = (b + ε) • S v - v := by
    have := congrArg (fun F => F v) hrel
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply] at this
    rw [hX'v, map_smul] at this
    rw [eq_sub_iff_add_eq]; exact this.symm
  set w := S v with hwdef
  set u := w - ε • v with hudef
  have hXu : X u = (b + ε) • u := by
    have e1 : (b + ε) * ε = ε * b + 1 := by linear_combination hε2
    rw [hudef, map_sub, map_smul, hXw, hXv, smul_sub, smul_smul, smul_smul, e1]
    simp only [add_smul, one_smul]
    abel
  have huv : X7_ip P u v = 0 := by
    have := hXsa u v
    rw [hXu, hXv, X7_ip_smul_left, X7_ip_smul_right, star_add, hb, hεs] at this
    have h2 : ε * X7_ip P u v = 0 := by linear_combination this
    exact (mul_eq_zero.1 h2).resolve_left hε0
  have hvu : X7_ip P v u = 0 := by
    have := hXsa v u
    rw [hXu, hXv, X7_ip_smul_left, X7_ip_smul_right, hb] at this
    have h2 : ε * X7_ip P v u = 0 := by linear_combination -this
    exact (mul_eq_zero.1 h2).resolve_left hε0
  have hw : X7_ip P w w = X7_ip P v v := hS v v
  have hwd : w = u + ε • v := by rw [hudef]; abel
  rw [hwd, X7_ip_add_left, X7_ip_add_right, X7_ip_add_right, X7_ip_smul_left,
    X7_ip_smul_right, X7_ip_smul_left, X7_ip_smul_right, huv, hvu, hεs] at hw
  have huu : X7_ip P u u = 0 := by linear_combination hw - (X7_ip P v v) * hε2
  have hu0 := X7_ip_self P h1 u huu
  rw [hwd, hu0, zero_add]

lemma X7_perm1 {n : ℕ} (j k k1 : Fin n) (hk : k1.val = k.val + 1) (hj : j.val < k.val) :
    Equiv.swap k k1 * Equiv.swap j k1 = Equiv.swap j k * Equiv.swap k k1 := by
  have hjk : j ≠ k := fun h => by rw [h] at hj; omega
  have hjk1 : j ≠ k1 := fun h => by rw [h] at hj; omega
  have h := Equiv.swap_apply_apply (Equiv.swap k k1) j k1
  rw [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hjk hjk1, Equiv.swap_apply_right] at h
  rw [h, mul_assoc, Equiv.swap_mul_self, mul_one]

lemma X7_braid {n : ℕ} (p0 p1 p2 : Fin n) (h1 : p1.val = p0.val + 1) (h2 : p2.val = p0.val + 2) :
    Equiv.swap p0 p1 * Equiv.swap p1 p2 * Equiv.swap p0 p1 =
      Equiv.swap p1 p2 * Equiv.swap p0 p1 * Equiv.swap p1 p2 := by
  have h02 : p2 ≠ p0 := fun h => by rw [h] at h2; omega
  have h12 : p2 ≠ p1 := fun h => by rw [h] at h2; omega
  have h01 : p0 ≠ p1 := fun h => by rw [h] at h1; omega
  have ha := Equiv.swap_apply_apply (Equiv.swap p0 p1) p1 p2
  rw [Equiv.swap_inv, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne h02 h12] at ha
  have hb := Equiv.swap_apply_apply (Equiv.swap p1 p2) p0 p1
  rw [Equiv.swap_inv, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h01 h02.symm] at hb
  rw [← ha, ← hb]

lemma X7_rel {n : ℕ} (k k1 : Fin n) (hk : k1.val = k.val + 1) :
    MonoidAlgebra.single (Equiv.swap k k1) (1 : ℂ) * yjm k1 =
      yjm k * MonoidAlgebra.single (Equiv.swap k k1) (1 : ℂ) + 1 := by
  simp only [yjm, swapAlgebraElement, Finset.sum_mul, Finset.mul_sum,
    MonoidAlgebra.single_mul_single, mul_one, Finset.sum_filter]
  have h1 : (1 : SymmetricAlgebra n) =
      ∑ j : Fin n, if j = k then (1 : SymmetricAlgebra n) else 0 := by simp
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hjk : j.val < k.val
  · have hlt1 : j < k1 := by rw [Fin.lt_def]; omega
    have hlt : j < k := hjk
    have hne : j ≠ k := by intro h; subst h; omega
    rw [if_pos hlt1, if_pos hlt, if_neg hne, add_zero, MonoidAlgebra.single_mul_single,
      MonoidAlgebra.single_mul_single, X7_perm1 j k k1 hk hjk]
  · by_cases hjk' : j = k
    · subst hjk'
      have hlt1 : j < k1 := by rw [Fin.lt_def]; omega
      rw [if_pos hlt1, if_neg (lt_irrefl j), if_pos rfl, zero_mul, zero_add,
        MonoidAlgebra.single_mul_single, Equiv.swap_mul_self, mul_one, MonoidAlgebra.one_def]
    · have hn1 : ¬ j < k1 := by
        rw [Fin.lt_def]; intro h; apply hjk'; ext; omega
      have hn : ¬ j < k := hjk
      rw [if_neg hn1, if_neg hn, if_neg hjk']
      simp

theorem X7_main {n : ℕ} (alpha : Fin n → ℂ) (i : ℕ) (hi : i + 2 < n)
    (hfirst : alpha ⟨i, by omega⟩ = alpha ⟨i + 2, hi⟩)
    (hnext : alpha ⟨i + 1, by omega⟩ = alpha ⟨i, by omega⟩ + 1) :
    alpha ∉ spectrum n := by
  rintro ⟨d, rho, -, v, hv0, hvw⟩
  set P : Equiv.Perm (Fin n) → Module.End ℂ (Fin d → ℂ) :=
    fun g => rho (MonoidAlgebra.single g 1) with hP
  have hmul : ∀ g h z, P g (P h z) = P (g * h) z := by
    intro g h z
    simp only [hP, ← Module.End.mul_apply, ← map_mul, MonoidAlgebra.single_mul_single, mul_one]
  have h1 : P 1 = 1 := by
    simp only [hP]; rw [← MonoidAlgebra.one_def, map_one]
  have hinvol : ∀ t : Equiv.Perm (Fin n), t * t = 1 → ∀ x y,
      X7_ip P (P t x) y = X7_ip P x (P t y) := by
    intro t ht x y
    rw [← X7_ip_inv P hmul t (P t x) y, hmul, ht, h1]
    rfl
  have hsa : ∀ (j : Fin n) x y, X7_ip P (rho (yjm j) x) y = X7_ip P x (rho (yjm j) y) := by
    intro j x y
    simp only [yjm, swapAlgebraElement, map_sum, LinearMap.sum_apply]
    rw [X7_ip_sum_left, X7_ip_sum_right]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact hinvol _ (Equiv.swap_mul_self _ _) x y
  set p0 : Fin n := ⟨i, by omega⟩
  set p1 : Fin n := ⟨i + 1, by omega⟩
  set p2 : Fin n := ⟨i + 2, hi⟩
  have hrelP : ∀ k k1 : Fin n, k1.val = k.val + 1 →
      P (Equiv.swap k k1) * rho (yjm k1) = rho (yjm k) * P (Equiv.swap k k1) + 1 := by
    intro k k1 hk
    simp only [hP]
    rw [← map_mul, ← map_mul, ← map_one rho, ← map_add, X7_rel k k1 hk]
  have hS1 := X7_key P h1 (rho (yjm p0)) (rho (yjm p1)) (P (Equiv.swap p0 p1))
    (hsa p0) (X7_ip_inv P hmul _) (hrelP p0 p1 rfl) (alpha p0) 1 (Or.inl rfl) v hv0
    (hvw p0) (by rw [hvw p1, show alpha p1 = alpha p0 + 1 from hnext])
  have hS2 := X7_key P h1 (rho (yjm p1)) (rho (yjm p2)) (P (Equiv.swap p1 p2))
    (hsa p1) (X7_ip_inv P hmul _) (hrelP p1 p2 rfl) (alpha p1) (-1) (Or.inr rfl) v hv0
    (hvw p1) (by rw [hvw p2]; congr 1; change alpha p2 = alpha p1 + -1;
                 rw [show alpha p1 = alpha p0 + 1 from hnext, ← hfirst]; ring)
  have hbr := X7_braid p0 p1 p2 rfl rfl
  have e1 : P (Equiv.swap p0 p1 * Equiv.swap p1 p2 * Equiv.swap p0 p1) v = -v := by
    rw [← hmul, ← hmul, hS1, one_smul, hS2, map_smul, hS1, one_smul, neg_one_smul]
  have e2 : P (Equiv.swap p1 p2 * Equiv.swap p0 p1 * Equiv.swap p1 p2) v = v := by
    rw [← hmul, ← hmul, hS2, map_smul, hS1, one_smul, map_smul, hS2, smul_smul]; norm_num
  rw [hbr, e2] at e1
  apply hv0
  have : (2 : ℂ) • v = 0 := by rw [two_smul]; nth_rewrite 1 [e1]; exact neg_add_cancel v
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

end X7B17L52

end

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Renew46.P26 X7B17L52 in
theorem solution {n : ℕ} (alpha : Fin n → ℂ) (i : ℕ) (hi : i + 2 < n)
    (hfirst : alpha ⟨i, by omega⟩ = alpha ⟨i + 2, hi⟩)
    (hnext : alpha ⟨i + 1, by omega⟩ = alpha ⟨i, by omega⟩ + 1) :
    alpha ∉ spectrum n :=
  X7_main alpha i hi hfirst hnext

end
