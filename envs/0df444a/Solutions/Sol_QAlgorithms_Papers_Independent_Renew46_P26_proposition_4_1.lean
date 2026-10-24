-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T10:06:34.299346+00:00
-- url     : https://prove2.me/submissions/7396fae7-1b9b-425e-96be-f82cd66c2e52

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

open scoped BigOperators

namespace X7B17P41
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

lemma X7_ip_sub_left (x x' y : Fin d → ℂ) :
    X7_ip P (x - x') y = X7_ip P x y - X7_ip P x' y := by
  simp [X7_ip, map_sub, sub_mul, Finset.sum_sub_distrib]

def X7_P {n d : ℕ} (rho : SymmetricAlgebra n →ₐ[ℂ] Module.End ℂ (Fin d → ℂ))
    (g : Equiv.Perm (Fin n)) : Module.End ℂ (Fin d → ℂ) :=
  rho (MonoidAlgebra.single g 1)

section
variable {n : ℕ} (rho : SymmetricAlgebra n →ₐ[ℂ] Module.End ℂ (Fin d → ℂ))

lemma X7_P_mul (g h : Equiv.Perm (Fin n)) (z : Fin d → ℂ) :
    X7_P rho g (X7_P rho h z) = X7_P rho (g * h) z := by
  simp only [X7_P, ← Module.End.mul_apply, ← map_mul, MonoidAlgebra.single_mul_single, mul_one]

lemma X7_P_one : X7_P rho 1 = 1 := by
  simp only [X7_P]; rw [← MonoidAlgebra.one_def, map_one]

lemma X7_hsa (j : Fin n) (x y : Fin d → ℂ) :
    X7_ip (X7_P rho) (rho (yjm j) x) y = X7_ip (X7_P rho) x (rho (yjm j) y) := by
  have hinvol : ∀ t : Equiv.Perm (Fin n), t * t = 1 → ∀ x y,
      X7_ip (X7_P rho) (X7_P rho t x) y = X7_ip (X7_P rho) x (X7_P rho t y) := by
    intro t ht x y
    rw [← X7_ip_inv (X7_P rho) (X7_P_mul rho) t (X7_P rho t x) y, X7_P_mul, ht, X7_P_one]
    rfl
  simp only [yjm, swapAlgebraElement, map_sum, LinearMap.sum_apply]
  rw [X7_ip_sum_left, X7_ip_sum_right]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact hinvol _ (Equiv.swap_mul_self _ _) x y

lemma X7_relP (k k1 : Fin n) (hk : k1.val = k.val + 1) :
    X7_P rho (Equiv.swap k k1) * rho (yjm k1) = rho (yjm k) * X7_P rho (Equiv.swap k k1) + 1 := by
  simp only [X7_P]
  rw [← map_mul, ← map_mul, ← map_one rho, ← map_add, X7_rel k k1 hk]

lemma X7_SS (k k1 : Fin n) :
    X7_P rho (Equiv.swap k k1) * X7_P rho (Equiv.swap k k1) = 1 := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, X7_P_mul, Equiv.swap_mul_self, X7_P_one]

lemma X7_real (j : Fin n) (b : ℂ) (v : Fin d → ℂ) (hv : v ≠ 0)
    (h : rho (yjm j) v = b • v) : star b = b := by
  have hvv : X7_ip (X7_P rho) v v ≠ 0 :=
    fun h0 => hv (X7_ip_self (X7_P rho) (X7_P_one rho) v h0)
  have := X7_hsa rho j v v
  rw [h, X7_ip_smul_left, X7_ip_smul_right] at this
  exact mul_right_cancel₀ hvv this

lemma X7_neq (k k1 : Fin n) (hk : k1.val = k.val + 1) (alpha : Fin n → ℂ) (v : Fin d → ℂ)
    (hv : IsWeightVector rho alpha v) : alpha k ≠ alpha k1 := by
  obtain ⟨hv0, hvw⟩ := hv
  intro hbc
  have hvv : X7_ip (X7_P rho) v v ≠ 0 :=
    fun h0 => hv0 (X7_ip_self (X7_P rho) (X7_P_one rho) v h0)
  have hb := X7_real rho k (alpha k) v hv0 (hvw k)
  set S := X7_P rho (Equiv.swap k k1)
  have hXw : rho (yjm k) (S v) = alpha k • S v - v := by
    have := congrArg (fun F => F v) (X7_relP rho k k1 hk)
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply] at this
    rw [hvw k1, map_smul, ← hbc] at this
    rw [eq_sub_iff_add_eq]; exact this.symm
  have := X7_hsa rho k (S v) v
  rw [hXw, hvw k, X7_ip_sub_left, X7_ip_smul_left, X7_ip_smul_right, hb] at this
  exact hvv (by linear_combination -this)

lemma X7_lt_iff (k k1 j l : Fin n) (hk : k1.val = k.val + 1) (hj0 : j ≠ k) (hj1 : j ≠ k1) :
    Equiv.swap k k1 l < j ↔ l < j := by
  have hj0' : j.val ≠ k.val := fun h => hj0 (Fin.ext h)
  have hj1' : j.val ≠ k1.val := fun h => hj1 (Fin.ext h)
  rw [Fin.lt_def, Fin.lt_def]
  by_cases hl0 : l = k
  · subst hl0; rw [Equiv.swap_apply_left]; omega
  · by_cases hl1 : l = k1
    · subst hl1; rw [Equiv.swap_apply_right]; omega
    · rw [Equiv.swap_apply_of_ne_of_ne hl0 hl1]

lemma X7_comm (k k1 j : Fin n) (hk : k1.val = k.val + 1) (hj0 : j ≠ k) (hj1 : j ≠ k1) :
    MonoidAlgebra.single (Equiv.swap k k1) (1 : ℂ) * yjm j =
      yjm j * MonoidAlgebra.single (Equiv.swap k k1) (1 : ℂ) := by
  simp only [yjm, swapAlgebraElement, Finset.sum_mul, Finset.mul_sum, Finset.sum_filter,
    mul_ite, ite_mul, mul_zero, zero_mul]
  set s := Equiv.swap k k1
  have hconj : ∀ l, s * Equiv.swap l j = Equiv.swap (s l) j * s := by
    intro l
    have h := Equiv.swap_apply_apply s l j
    rw [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hj0 hj1] at h
    rw [h, mul_assoc, Equiv.swap_mul_self, mul_one]
  have hL : ∀ l : Fin n, (if l < j then MonoidAlgebra.single s (1 : ℂ) *
      MonoidAlgebra.single (Equiv.swap l j) 1 else 0) =
      (fun m : Fin n => if m < j then MonoidAlgebra.single (Equiv.swap m j) (1 : ℂ) *
        MonoidAlgebra.single s 1 else 0) (s l) := by
    intro l
    simp only
    by_cases hl : l < j
    · rw [if_pos hl, if_pos ((X7_lt_iff k k1 j l hk hj0 hj1).2 hl),
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, hconj]
    · rw [if_neg hl, if_neg (fun h => hl ((X7_lt_iff k k1 j l hk hj0 hj1).1 h))]
  rw [Finset.sum_congr rfl (fun l _ => hL l)]
  exact Equiv.sum_comp s (fun m : Fin n => if m < j then
    MonoidAlgebra.single (Equiv.swap m j) (1 : ℂ) * MonoidAlgebra.single s 1
    else (0 : SymmetricAlgebra n))

lemma X7_commP (k k1 j : Fin n) (hk : k1.val = k.val + 1) (hj0 : j ≠ k) (hj1 : j ≠ k1) :
    X7_P rho (Equiv.swap k k1) * rho (yjm j) = rho (yjm j) * X7_P rho (Equiv.swap k k1) := by
  simp only [X7_P]
  rw [← map_mul, ← map_mul, X7_comm k k1 j hk hj0 hj1]

lemma X7_stepW (alpha : Fin n → ℂ) (v : Fin d → ℂ) (hv : IsWeightVector rho alpha v)
    (i : Adjacent n) (hne1 : alpha (nextPosition i) ≠ alpha i.val + 1)
    (hne2 : alpha (nextPosition i) ≠ alpha i.val - 1) :
    IsWeightVector rho (alpha ∘ adjacentPerm i)
      (X7_P rho (Equiv.swap i.val (nextPosition i)) v -
        (alpha (nextPosition i) - alpha i.val)⁻¹ • v) := by
  set k := i.val
  set k1 := nextPosition i
  have hk : k1.val = k.val + 1 := rfl
  have hkk1 : alpha k ≠ alpha k1 := X7_neq rho k k1 hk alpha v hv
  obtain ⟨hv0, hvw⟩ := hv
  set b := alpha k
  set c := alpha k1
  set r := c - b with hrdef
  have hr : r ≠ 0 := sub_ne_zero.2 (Ne.symm hkk1)
  set S := X7_P rho (Equiv.swap k k1)
  have hSS : S * S = 1 := X7_SS rho k k1
  have hrel : S * rho (yjm k1) = rho (yjm k) * S + 1 := X7_relP rho k k1 hk
  have hrel2 : rho (yjm k1) * S = S * rho (yjm k) + 1 := by
    calc rho (yjm k1) * S = S * (S * rho (yjm k1)) * S := by rw [← mul_assoc S S, hSS, one_mul]
      _ = S * (rho (yjm k) * S + 1) * S := by rw [hrel]
      _ = S * rho (yjm k) * (S * S) + S * S := by noncomm_ring
      _ = S * rho (yjm k) + 1 := by rw [hSS, mul_one]
  have hXSv : rho (yjm k) (S v) = c • S v - v := by
    have := congrArg (fun F => F v) hrel
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply] at this
    rw [hvw k1, map_smul] at this
    rw [eq_sub_iff_add_eq]; exact this.symm
  have hX'Sv : rho (yjm k1) (S v) = b • S v + v := by
    have := congrArg (fun F => F v) hrel2
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply] at this
    rw [this, hvw k, map_smul]
  refine ⟨?_, ?_⟩
  · intro hw
    have h1 : S v = r⁻¹ • v := sub_eq_zero.1 hw
    have h2 : S (S v) = v := by rw [← Module.End.mul_apply, hSS, Module.End.one_apply]
    rw [h1, map_smul, h1, smul_smul] at h2
    have h3 : (r⁻¹ * r⁻¹ - 1) • v = 0 := by rw [sub_smul, h2, one_smul, sub_self]
    have h4 : r⁻¹ * r⁻¹ - 1 = 0 := (smul_eq_zero.1 h3).resolve_right hv0
    have h5 : (r - 1) * (r + 1) = 0 := by
      field_simp at h4
      linear_combination -h4
    rcases mul_eq_zero.1 h5 with h | h
    · exact hne1 (by linear_combination h)
    · exact hne2 (by linear_combination h)
  · intro j
    by_cases hj0 : j = k
    · rw [hj0]
      simp only [Function.comp_apply, adjacentPerm]
      change _ = alpha (Equiv.swap k k1 k) • _
      rw [Equiv.swap_apply_left, map_sub, map_smul, hXSv, hvw k]
      have e : c * r⁻¹ = r⁻¹ * b + 1 := by rw [hrdef]; field_simp; ring
      rw [smul_sub, smul_smul, smul_smul, e, add_smul, one_smul]
      abel
    · by_cases hj1 : j = k1
      · rw [hj1]
        simp only [Function.comp_apply, adjacentPerm]
        change _ = alpha (Equiv.swap k k1 k1) • _
        rw [Equiv.swap_apply_right, map_sub, map_smul, hX'Sv, hvw k1]
        have e : r⁻¹ * c = b * r⁻¹ + 1 := by rw [hrdef]; field_simp; ring
        rw [smul_sub, smul_smul, smul_smul, e, add_smul, one_smul]
        abel
      · simp only [Function.comp_apply, adjacentPerm]
        change _ = alpha (Equiv.swap k k1 j) • _
        rw [Equiv.swap_apply_of_ne_of_ne hj0 hj1, map_sub, map_smul]
        have hc := congrArg (fun F => F v) (X7_commP rho k k1 j hk hj0 hj1)
        simp only [Module.End.mul_apply] at hc
        rw [← hc, hvw j, map_smul, smul_sub, smul_smul, smul_smul, mul_comm]

lemma X7_step (alpha beta : Fin n → ℂ) (v : Fin d → ℂ) (hv : IsWeightVector rho alpha v)
    (hstep : AdmissibleStep alpha beta) : ∃ w, IsWeightVector rho beta w := by
  obtain ⟨i, hne1, hne2, rfl⟩ := hstep
  exact ⟨_, X7_stepW rho alpha v hv i hne1 hne2⟩

lemma X7_reach (alpha beta : Fin n → ℂ) (v : Fin d → ℂ) (hv : IsWeightVector rho alpha v)
    (hab : AdmissiblyEquivalent alpha beta) : ∃ w, IsWeightVector rho beta w := by
  induction hab with
  | refl => exact ⟨v, hv⟩
  | tail _ hstep ih =>
    obtain ⟨w, hw⟩ := ih
    exact X7_step rho _ _ w hw hstep

lemma X7_yjm0 (h : 0 < n) : yjm (⟨0, h⟩ : Fin n) = 0 := by
  unfold yjm
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact absurd hj (by rw [Fin.lt_def]; simp)

lemma X7_weight0 (alpha : Fin n → ℂ) (v : Fin d → ℂ) (hv : IsWeightVector rho alpha v)
    (k : Fin n) (hk : k.val = 0) : alpha k = 0 := by
  obtain ⟨hv0, hvw⟩ := hv
  have h0 : 0 < n := by have := k.isLt; omega
  have hk' : k = ⟨0, h0⟩ := Fin.ext hk
  have := hvw k
  rw [hk', X7_yjm0 h0, map_zero, LinearMap.zero_apply] at this
  rw [hk']
  exact (smul_eq_zero.1 this.symm).resolve_right hv0

/-- shifted vector: entry `q` moved to position `m`. -/
def X7_gam (alpha : Fin n → ℂ) (q : Fin n) (m : ℕ) : Fin n → ℂ := fun j =>
  if j.val < m then alpha j else if j.val = m then alpha q
  else if j.val ≤ q.val then alpha ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
  else alpha j

lemma X7_gam_q (alpha : Fin n → ℂ) (q : Fin n) : X7_gam alpha q q.val = alpha := by
  funext j
  unfold X7_gam
  split_ifs with h1 h2 h3
  · rfl
  · rw [show q = j from Fin.ext h2.symm]
  · omega
  · rfl

lemma X7_gam_step (alpha : Fin n → ℂ) (q : Fin n) (m : ℕ) (hm : m + 1 ≤ q.val) :
    X7_gam alpha q m = X7_gam alpha q (m + 1) ∘
      adjacentPerm (⟨⟨m, by omega⟩, by simp; omega⟩ : Adjacent n) := by
  funext j
  simp only [Function.comp_apply, adjacentPerm, nextPosition]
  by_cases hj0 : j.val = m
  · have : j = ⟨m, by omega⟩ := Fin.ext hj0
    rw [this, Equiv.swap_apply_left]
    unfold X7_gam
    simp
  · by_cases hj1 : j.val = m + 1
    · have : j = ⟨m + 1, by omega⟩ := Fin.ext hj1
      rw [this, Equiv.swap_apply_right]
      unfold X7_gam
      simp only [lt_self_iff_false, if_false, Nat.lt_succ_self, if_true]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by simp; omega)]
      congr 1
    · have hne0 : j ≠ ⟨m, by omega⟩ := fun h => hj0 (by rw [h])
      have hne1 : j ≠ ⟨m + 1, by omega⟩ := fun h => hj1 (by rw [h])
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
      unfold X7_gam
      split_ifs <;> first | rfl | omega

lemma X7_gam_adm (alpha : Fin n → ℂ) (q : Fin n) (m : ℕ) (hm : m + 1 ≤ q.val)
    (H : ∀ p : Fin n, p < q → alpha p ≠ alpha q + 1 ∧ alpha p ≠ alpha q - 1) :
    AdmissibleStep (X7_gam alpha q (m + 1)) (X7_gam alpha q m) := by
  rw [X7_gam_step alpha q m hm]
  have hp := H ⟨m, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
  have e1 : X7_gam alpha q (m + 1) ⟨m + 1, by omega⟩ = alpha q := by unfold X7_gam; simp
  have e2 : X7_gam alpha q (m + 1) ⟨m, by omega⟩ = alpha ⟨m, by omega⟩ := by
    unfold X7_gam; simp
  refine ⟨_, ?_, ?_, rfl⟩
  · show X7_gam alpha q (m + 1) ⟨m + 1, by omega⟩ ≠ X7_gam alpha q (m + 1) ⟨m, by omega⟩ + 1
    rw [e1, e2]
    intro h; exact hp.2 (by rw [h]; ring)
  · show X7_gam alpha q (m + 1) ⟨m + 1, by omega⟩ ≠ X7_gam alpha q (m + 1) ⟨m, by omega⟩ - 1
    rw [e1, e2]
    intro h; exact hp.1 (by rw [h]; ring)

lemma X7_moveleft (alpha : Fin n → ℂ) (v : Fin d → ℂ) (hv : IsWeightVector rho alpha v)
    (q : Fin n) (hq : 0 < q.val)
    (H : ∀ p : Fin n, p < q → alpha p ≠ alpha q + 1 ∧ alpha p ≠ alpha q - 1) : False := by
  have key : ∀ t, t ≤ q.val → ∃ w, IsWeightVector rho (X7_gam alpha q (q.val - t)) w := by
    intro t
    induction t with
    | zero => intro _; rw [Nat.sub_zero, X7_gam_q]; exact ⟨v, hv⟩
    | succ t ih =>
      intro ht
      obtain ⟨w, hw⟩ := ih (by omega)
      have hm : q.val - (t + 1) + 1 = q.val - t := by omega
      rw [← hm] at hw
      exact X7_step rho _ _ w hw (X7_gam_adm alpha q _ (by omega) H)
  obtain ⟨w0, hw0⟩ := key q.val le_rfl
  rw [Nat.sub_self] at hw0
  have hq0 : X7_gam alpha q 0 ⟨0, by omega⟩ = 0 := X7_weight0 rho _ w0 hw0 _ rfl
  unfold X7_gam at hq0
  simp at hq0
  obtain ⟨w1, hw1⟩ := key (q.val - 1) (by omega)
  rw [show q.val - (q.val - 1) = 1 by omega] at hw1
  have hne := X7_neq rho ⟨0, by omega⟩ ⟨1, by omega⟩ rfl _ w1 hw1
  apply hne
  unfold X7_gam
  simp only [Nat.zero_lt_one, if_true, lt_self_iff_false, if_false]
  rw [X7_weight0 rho alpha v hv ⟨0, by omega⟩ rfl, hq0]

lemma X7_integral (alpha : Fin n → ℂ) (v : Fin d → ℂ) (hv : IsWeightVector rho alpha v) :
    ∀ j : Fin n, ∃ z : ℤ, alpha j = (z : ℂ) := by
  intro j
  induction' hjv : j.val using Nat.strong_induction_on with m ih generalizing j
  by_cases hm : m = 0
  · exact ⟨0, by rw [X7_weight0 rho alpha v hv j (by omega)]; simp⟩
  · by_cases hex : ∃ p : Fin n, p < j ∧ (alpha p = alpha j + 1 ∨ alpha p = alpha j - 1)
    · obtain ⟨p, hp, hpv⟩ := hex
      obtain ⟨z, hz⟩ := ih p.val (by rw [← hjv]; exact hp) p rfl
      rcases hpv with h | h
      · exact ⟨z - 1, by push_cast; rw [← hz, h]; ring⟩
      · exact ⟨z + 1, by push_cast; rw [← hz, h]; ring⟩
    · exfalso
      push Not at hex
      exact X7_moveleft rho alpha v hv j (by omega) hex

end

theorem X7_main {n d : ℕ}
    (rho : SymmetricAlgebra n →ₐ[ℂ] Module.End ℂ (Fin d → ℂ))
    (hrho : IsIrreducibleAlgebra rho) (alpha : Fin n → ℂ) (v : Fin d → ℂ)
    (hv : IsWeightVector rho alpha v) :
    (∀ j : Fin n, ∃ z : ℤ, alpha j = (z : ℂ)) ∧
    (∀ i : Adjacent n, alpha i.val ≠ alpha (nextPosition i)) ∧
    (∀ i : Adjacent n,
      (alpha (nextPosition i) = alpha i.val + 1 → rho (adjacentElement i) v = v) ∧
      (alpha (nextPosition i) = alpha i.val - 1 → rho (adjacentElement i) v = -v)) ∧
    (∀ i : Adjacent n, alpha (nextPosition i) ≠ alpha i.val + 1 →
      alpha (nextPosition i) ≠ alpha i.val - 1 →
      let beta := alpha ∘ adjacentPerm i
      let r := alpha (nextPosition i) - alpha i.val
      let w := rho (adjacentElement i) v - r⁻¹ • v
      beta ∈ spectrum n ∧ SameIrreducible alpha beta ∧
      IsWeightVector rho beta w ∧ LinearIndependent ℂ ![v, w] ∧
      rho (adjacentElement i) v = r⁻¹ • v + w ∧
      rho (adjacentElement i) w = (1 - (r⁻¹)^2) • v - r⁻¹ • w) := by
  refine ⟨X7_integral rho alpha v hv, fun i => X7_neq rho i.val (nextPosition i) rfl alpha v hv,
    ?_, ?_⟩
  · intro i
    constructor
    · intro h
      have := X7_key (X7_P rho) (X7_P_one rho) (rho (yjm i.val)) (rho (yjm (nextPosition i)))
        (X7_P rho (Equiv.swap i.val (nextPosition i))) (X7_hsa rho _)
        (X7_ip_inv _ (X7_P_mul rho) _) (X7_relP rho _ _ rfl) (alpha i.val) 1 (Or.inl rfl) v hv.1
        (hv.2 _) (by rw [hv.2, h])
      rw [one_smul] at this
      exact this
    · intro h
      have := X7_key (X7_P rho) (X7_P_one rho) (rho (yjm i.val)) (rho (yjm (nextPosition i)))
        (X7_P rho (Equiv.swap i.val (nextPosition i))) (X7_hsa rho _)
        (X7_ip_inv _ (X7_P_mul rho) _) (X7_relP rho _ _ rfl) (alpha i.val) (-1) (Or.inr rfl) v
        hv.1 (hv.2 _) (by rw [hv.2, h, sub_eq_add_neg])
      rw [neg_one_smul] at this
      exact this
  · intro i h1 h2 beta r w
    have hw : IsWeightVector rho beta w := X7_stepW rho alpha v hv i h1 h2
    have hS : rho (adjacentElement i) = X7_P rho (Equiv.swap i.val (nextPosition i)) := rfl
    have hwdef : w = X7_P rho (Equiv.swap i.val (nextPosition i)) v - r⁻¹ • v := rfl
    refine ⟨⟨d, rho, hrho, w, hw⟩, ⟨d, rho, hrho, v, w, hv, hw⟩, hw, ?_, ?_, ?_⟩
    · rw [LinearIndependent.pair_iff]
      intro s t hst
      have hb : beta i.val = alpha (nextPosition i) := by
        simp only [beta, Function.comp_apply, adjacentPerm, Equiv.swap_apply_left]
      have e := congrArg (rho (yjm i.val)) hst
      rw [map_add, map_smul, map_smul, hv.2, hw.2, hb, map_zero] at e
      have h3 : (s * (alpha (nextPosition i) - alpha i.val)) • v =
          alpha (nextPosition i) • (s • v + t • w) -
            (s • alpha i.val • v + t • alpha (nextPosition i) • w) := by module
      rw [hst, e, smul_zero, sub_zero] at h3
      have hne := X7_neq rho i.val (nextPosition i) rfl alpha v hv
      have hs : s = 0 := by
        rcases smul_eq_zero.1 h3 with h | h
        · exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 (Ne.symm hne))
        · exact absurd h hv.1
      refine ⟨hs, ?_⟩
      rw [hs, zero_smul, zero_add] at hst
      exact (smul_eq_zero.1 hst).resolve_right hw.1
    · rw [hwdef, hS]; abel
    · rw [hwdef, hS, map_sub, map_smul, ← Module.End.mul_apply, X7_SS, Module.End.one_apply]
      module

end X7B17P41

end

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Renew46.P26 X7B17P41 in
theorem solution {n d : ℕ}
    (rho : SymmetricAlgebra n →ₐ[ℂ] Module.End ℂ (Fin d → ℂ))
    (hrho : IsIrreducibleAlgebra rho) (alpha : Fin n → ℂ) (v : Fin d → ℂ)
    (hv : IsWeightVector rho alpha v) :
    (∀ j : Fin n, ∃ z : ℤ, alpha j = (z : ℂ)) ∧
    (∀ i : Adjacent n, alpha i.val ≠ alpha (nextPosition i)) ∧
    (∀ i : Adjacent n,
      (alpha (nextPosition i) = alpha i.val + 1 → rho (adjacentElement i) v = v) ∧
      (alpha (nextPosition i) = alpha i.val - 1 → rho (adjacentElement i) v = -v)) ∧
    (∀ i : Adjacent n, alpha (nextPosition i) ≠ alpha i.val + 1 →
      alpha (nextPosition i) ≠ alpha i.val - 1 →
      let beta := alpha ∘ adjacentPerm i
      let r := alpha (nextPosition i) - alpha i.val
      let w := rho (adjacentElement i) v - r⁻¹ • v
      beta ∈ spectrum n ∧ SameIrreducible alpha beta ∧
      IsWeightVector rho beta w ∧ LinearIndependent ℂ ![v, w] ∧
      rho (adjacentElement i) v = r⁻¹ • v + w ∧
      rho (adjacentElement i) w = (1 - (r⁻¹)^2) • v - r⁻¹ • w) :=
  X7_main rho hrho alpha v hv

end
