-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P11.generic_field_characterization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:43:18.739996+00:00
-- url     : https://prove2.me/submissions/efe1f51b-3e70-428a-a1cc-721b57820127

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11
import Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_rational_weights_schur_identity
import Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_two_strand_spanning
import Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_generic_field_schur_formula

noncomputable section

section X8part_a
open scoped BigOperators Classical
open Polynomial

namespace X8GF

variable {F : Type*} [Field F]

/-- Lagrange partial fractions, evaluated off the nodes. -/
lemma pf {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → F) (hv : Function.Injective v)
    (f : F[X]) (hf : f.degree < Fintype.card ι) (z : F) (hz : ∀ i, z ≠ v i) :
    f.eval z = (∏ i, (z - v i)) *
      ∑ i, f.eval (v i) * ((∏ j ∈ Finset.univ.erase i, (v i - v j))⁻¹ * (z - v i)⁻¹) := by
  have hinj : Set.InjOn v (Finset.univ : Finset ι) := fun a _ b _ h => hv h
  have h := Lagrange.eq_interpolate (s := Finset.univ) hinj (by simpa using hf)
  conv_lhs => rw [h]
  rw [Lagrange.interpolate_apply, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, Lagrange.eval_basis_not_at_node (Finset.mem_univ i) (hz i),
    Lagrange.eval_nodal, Lagrange.nodalWeight, Finset.prod_inv_distrib]
  ring

lemma prod_erase_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → F) (a : ι) :
    ∏ j ∈ Finset.univ.erase a, g j = ∏ j, (if j = a then 1 else g j) := by
  rw [← Finset.prod_erase Finset.univ (f := fun j => if j = a then 1 else g j) (a := a)
    (by simp)]
  exact Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]

/-- The weights `γ_i`, written as in `weightGamma`. -/
def gam {r : ℕ} (u : Fin r → F) (i : Fin r) : F :=
  (2 * u i - (-1 : F) ^ r) * ∏ j ∈ Finset.univ.erase i, (u i + u j) / (u i - u j)

lemma deg_diff {r : ℕ} (u : Fin r → F) :
    (∏ k, (X + C (u k)) - ∏ k, (X - C (u k)) : F[X]) = 0 ∨
      (∏ k, (X + C (u k)) - ∏ k, (X - C (u k)) : F[X]).natDegree < r := by
  by_cases h0 : (∏ k, (X + C (u k)) - ∏ k, (X - C (u k)) : F[X]) = 0
  · exact Or.inl h0
  right
  have h1 : (∏ k, (X + C (u k)) : F[X]).Monic := monic_prod_of_monic _ _ fun k _ => monic_X_add_C _
  have h2 : (∏ k, (X - C (u k)) : F[X]).Monic := monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _
  have d1 : (∏ k, (X + C (u k)) : F[X]).natDegree = r := by
    rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_add_C _]; simp
  have d2 : (∏ k, (X - C (u k)) : F[X]).natDegree = r := by
    rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C _]; simp
  have := degree_sub_lt_left (p := (∏ k, (X + C (u k)) : F[X])) (q := ∏ k, (X - C (u k)))
    (by rw [degree_eq_natDegree h1.ne_zero, degree_eq_natDegree h2.ne_zero, d1, d2]) h1.ne_zero
    (by rw [h1.leadingCoeff, h2.leadingCoeff])
  rw [degree_eq_natDegree h1.ne_zero, d1] at this
  exact (natDegree_lt_iff_degree_lt h0).mpr this

/-- Nodes `0, u_1, ..., u_r`. -/
def vv {r : ℕ} (u : Fin r → F) : Option (Fin r) → F
  | none => 0
  | some i => u i

@[simp] lemma vv_none {r : ℕ} (u : Fin r → F) : vv u none = 0 := rfl
@[simp] lemma vv_some {r : ℕ} (u : Fin r → F) (i : Fin r) : vv u (some i) = u i := rfl

lemma erase_none {r : ℕ} (g : Option (Fin r) → F) :
    ∏ o ∈ Finset.univ.erase none, g o = ∏ k, g (some k) := by
  rw [prod_erase_ite, Fintype.prod_option]; simp

lemma erase_some {r : ℕ} (g : Option (Fin r) → F) (i : Fin r) :
    ∏ o ∈ Finset.univ.erase (some i), g o = g none * ∏ k ∈ Finset.univ.erase i, g (some k) := by
  rw [prod_erase_ite, Fintype.prod_option, prod_erase_ite]; simp

/-- The key partial-fraction identity: `∑_i γ_i/(u_i+u_j) = 1 + 1/(2u_j)`. -/
theorem ident {r : ℕ} (u : Fin r → F) (hd : Function.Injective u)
    (hs : ∀ i j, u i + u j ≠ 0) (j : Fin r) :
    ∑ i, gam u i / (u i + u j) = 1 + 1 / (2 * u j) := by
  set c : F := (-1 : F) ^ r with hc
  have hc2 : c * c = 1 := by rw [hc, ← pow_add, ← two_mul, pow_mul]; simp
  have hc0 : c ≠ 0 := by rw [hc]; exact pow_ne_zero _ (by norm_num)
  have hu0 : ∀ k, u k ≠ 0 := fun k h => hs k k (by rw [h, add_zero])
  have hv : Function.Injective (vv u) := by
    rintro (_ | a) (_ | b) h
    · rfl
    · exact absurd h.symm (hu0 b)
    · exact absurd h (hu0 a)
    · simp only [vv_some] at h; rw [hd h]
  let f : F[X] := C 2 * X * (∏ k, (X + C (u k)) - ∏ k, (X - C (u k))) - C c * ∏ k, (X + C (u k))
  have hf : f.degree < Fintype.card (Option (Fin r)) := by
    rw [Fintype.card_option, Fintype.card_fin]
    have hn : f.natDegree ≤ r := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · rcases deg_diff u with h | h
        · rw [h, mul_zero, natDegree_zero]; exact Nat.zero_le _
        refine natDegree_mul_le.trans ?_
        have : (C (2 : F) * X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
        omega
      · refine (natDegree_C_mul_le _ _).trans (le_of_eq ?_)
        rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_add_C _]; simp
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hn)
  have hz : ∀ o, -u j ≠ vv u o := by
    rintro (_ | a)
    · simpa using hu0 j
    · intro h; simp only [vv_some] at h
      exact hs a j (by rw [← h]; ring)
  have key := pf (vv u) hv f hf (-u j) hz
  have ev : ∀ z : F, f.eval z = 2 * z * (∏ k, (z + u k) - ∏ k, (z - u k)) - c * ∏ k, (z + u k) := by
    intro z; simp [f, eval_prod]
  have hP : ∏ k, (-u j + u k) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by ring)
  have hQ : ∀ i, ∏ k, (u i - u k) = 0 := fun i =>
    Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
  set P := ∏ k, (-u j - u k) with hPdef
  have hPne : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => by
    intro h; exact hs j k (by linear_combination -h)
  have hpu : ∏ k, u k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hu0 k
  have hden : ∀ i : Fin r, ∏ k ∈ Finset.univ.erase i, (u i - u k) ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hk (hd h).symm
  have hlhs : f.eval (-u j) = 2 * u j * P := by
    rw [ev, hP, hPdef]; ring
  have hnod : ∏ o, (-u j - vv u o) = -u j * P := by
    rw [Fintype.prod_option]; simp [hPdef]
  have h0 : f.eval (vv u none) * ((∏ o ∈ Finset.univ.erase none, (vv u none - vv u o))⁻¹ *
      (-u j - vv u none)⁻¹) = 1 / u j := by
    rw [erase_none, vv_none, ev]
    have e2 : ∏ x : Fin r, (-u x) = c * ∏ k, u k := by
      rw [Finset.prod_neg]; simp [hc]
    simp only [vv_some, zero_add, zero_sub, mul_zero, zero_mul]
    rw [e2]
    field_simp [hc0, hpu, hu0 j]
    ring
  have h1 : ∀ i : Fin r, f.eval (vv u (some i)) * ((∏ o ∈ Finset.univ.erase (some i),
      (vv u (some i) - vv u o))⁻¹ * (-u j - vv u (some i))⁻¹) = -2 * (gam u i / (u i + u j)) := by
    intro i
    rw [erase_some, vv_some, ev, hQ i, vv_none]
    simp only [vv_some]
    have e3 : ∏ k, (u i + u k) = 2 * u i * ∏ k ∈ Finset.univ.erase i, (u i + u k) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]; ring
    have hij : u i + u j ≠ 0 := hs i j
    have hneg : -u j - u i ≠ 0 := by intro h; exact hij (by linear_combination -h)
    rw [e3, gam, Finset.prod_div_distrib, ← hc]
    field_simp [hu0 i, hden i, hij, hneg]
    ring
  rw [hlhs, hnod, Fintype.sum_option, h0, Finset.sum_congr rfl (fun i _ => h1 i),
    ← Finset.mul_sum] at key
  have huj := hu0 j
  have h2 : (2 : F) * u j ≠ 0 := by rw [two_mul]; exact hs j j
  field_simp at key
  set S := ∑ i, gam u i / (u i + u j)
  have hS : 2 * u j * S = 2 * u j + 1 := by linear_combination -key
  have h2' : (2 : F) ≠ 0 := left_ne_zero_of_mul h2
  calc S = (2 * u j * S) / (2 * u j) := by field_simp
    _ = (2 * u j + 1) / (2 * u j) := by rw [hS]
    _ = 1 + 1 / (2 * u j) := by field_simp

end X8GF

end X8part_a

section X8part_b
open scoped BigOperators Classical
open Matrix

namespace X8GF

variable {F : Type*} [Field F] {r : ℕ} (u : Fin r → F)

def Xm : Matrix (Fin r) (Fin r) F := diagonal u
def Em : Matrix (Fin r) (Fin r) F := of fun _ i => gam u i
def Sm : Matrix (Fin r) (Fin r) F := of fun j i => (gam u i - if j = i then 1 else 0) / (u i + u j)

variable {u}

lemma SX (hs : ∀ i j, u i + u j ≠ 0) : Sm u * Xm u + Xm u * Sm u = Em u - 1 := by
  ext j i
  simp only [Sm, Xm, Em, Matrix.add_apply, mul_diagonal, diagonal_mul, of_apply, Matrix.sub_apply, one_apply]
  have := hs i j
  field_simp

lemma rowsum (hd : Function.Injective u) (hs : ∀ i j, u i + u j ≠ 0) (j : Fin r) :
    ∑ k, Sm u j k = 1 := by
  simp only [Sm, of_apply, sub_div, Finset.sum_sub_distrib]
  rw [ident u hd hs j]
  have : ∑ k : Fin r, (if j = k then (1 : F) else 0) / (u k + u j) = 1 / (u j + u j) := by
    simp only [ite_div, zero_div]; rw [Finset.sum_ite_eq]; simp
  rw [this]
  have h2 : u j + u j ≠ 0 := hs j j
  rw [← two_mul]
  ring

lemma SE (hd : Function.Injective u) (hs : ∀ i j, u i + u j ≠ 0) : Sm u * Em u = Em u := by
  ext j i
  simp only [mul_apply, Em, of_apply]
  rw [← Finset.sum_mul, rowsum hd hs, one_mul]

lemma ES (hd : Function.Injective u) (hs : ∀ i j, u i + u j ≠ 0) : Em u * Sm u = Em u := by
  ext j i
  simp only [mul_apply, Em, Sm, of_apply]
  have h : ∀ k, gam u k * ((gam u i - if k = i then 1 else 0) / (u i + u k)) =
      gam u i * (gam u k / (u k + u i)) - (if k = i then gam u i / (u i + u i) else 0) := by
    intro k
    have := hs i k
    split_ifs with hk
    · subst hk; field_simp; try ring
    · rw [add_comm (u k)]; field_simp; ring
  rw [Finset.sum_congr rfl fun k _ => h k, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ident u hd hs i, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have h2 : u i + u i ≠ 0 := hs i i
  rw [← two_mul] at h2 ⊢
  field_simp
  ring

lemma gam_eq_zero_iff (hd : Function.Injective u) (hs : ∀ i j, u i + u j ≠ 0) (i : Fin r) :
    gam u i = 0 ↔ 2 * u i = (-1 : F) ^ r := by
  rw [gam, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exfalso
      rw [Finset.prod_eq_zero_iff] at h
      obtain ⟨k, hk, h⟩ := h
      have hne : u i - u k ≠ 0 := sub_ne_zero.mpr fun e => Finset.ne_of_mem_erase hk (hd e).symm
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · exact hs i k h
      · exact hne h
  · exact Or.inl

lemma SS (hd : Function.Injective u) (hs : ∀ i j, u i + u j ≠ 0) : Sm u * Sm u = 1 := by
  have hcomm : Sm u * Sm u * Xm u = Xm u * (Sm u * Sm u) := by
    have e : Sm u * Sm u * Xm u - Xm u * (Sm u * Sm u) =
        Sm u * (Sm u * Xm u + Xm u * Sm u) - (Sm u * Xm u + Xm u * Sm u) * Sm u := by noncomm_ring
    rw [SX hs, mul_sub, sub_mul, SE hd hs, ES hd hs] at e
    rw [← sub_eq_zero, e]; noncomm_ring
  have hoff : ∀ j i, j ≠ i → (Sm u * Sm u) j i = 0 := by
    intro j i hji
    have := congrFun (congrFun hcomm j) i
    simp only [Xm, mul_diagonal, diagonal_mul] at this
    have hne : u i - u j ≠ 0 := sub_ne_zero.mpr fun e => hji (hd e).symm
    have : (Sm u * Sm u) j i * (u i - u j) = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hne
  ext j i
  rw [one_apply]
  split_ifs with hji
  swap
  · exact hoff j i hji
  subst hji
  by_cases hg : gam u j = 0
  · -- column j of S is a multiple of the basis vector
    have hcol : ∀ k, Sm u k j = if k = j then -1 / (2 * u j) else 0 := by
      intro k
      simp only [Sm, of_apply, hg, zero_sub]
      split_ifs with hk
      · subst hk; rw [two_mul]
      · simp
    rw [mul_apply, Finset.sum_eq_single j]
    · rw [hcol j, if_pos rfl]
      have h2 := (gam_eq_zero_iff hd hs j).mp hg
      have h3 : (2 * u j) * (2 * u j) = 1 := by
        rw [h2, ← pow_add, ← two_mul, pow_mul]; simp
      have h4 : 2 * u j ≠ 0 := by rw [two_mul]; exact hs j j
      rw [div_mul_div_comm, h3]; norm_num
    · intro k _ hk; rw [hcol k, if_neg hk, mul_zero]
    · simp
  · -- use E * S * S = E
    have h := congrFun (congrFun (show Em u * (Sm u * Sm u) = Em u by
      rw [← mul_assoc, ES hd hs, ES hd hs]) j) j
    rw [mul_apply, Finset.sum_eq_single j] at h
    · simp only [Em, of_apply] at h
      have : gam u j * ((Sm u * Sm u) j j - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hg
      · linear_combination h'
    · intro k _ hk; rw [hoff k j hk, mul_zero]
    · simp

lemma EXE (a : ℕ) : Em u * Xm u ^ a * Em u = (∑ i, gam u i * u i ^ a) • Em u := by
  rw [Xm, diagonal_pow]
  ext j i
  rw [mul_apply]
  simp only [mul_diagonal, Em, Matrix.smul_apply, smul_eq_mul, of_apply, Pi.pow_apply]
  rw [Finset.sum_mul]

lemma cyc : (List.ofFn fun j : Fin r => Xm u - algebraMap F (Matrix (Fin r) (Fin r) F) (u j)).prod
    = 0 := by
  have e : (fun j : Fin r => Xm u - algebraMap F (Matrix (Fin r) (Fin r) F) (u j)) =
      fun j => diagonalRingHom (Fin r) F (fun k => u k - u j) := by
    funext j
    ext a b
    simp [Xm, algebraMap_eq_diagonal, diagonal_apply]
    split_ifs <;> simp
  rw [e, show (List.ofFn fun j : Fin r => diagonalRingHom (Fin r) F (fun k => u k - u j)) =
    List.ofFn ((diagonalRingHom (Fin r) F) ∘ fun j k => u k - u j) from rfl,
    ← List.map_ofFn, ← map_list_prod, List.prod_ofFn]
  ext a b
  simp only [diagonalRingHom_apply, diagonal_apply, Matrix.zero_apply]
  split_ifs
  · rw [Finset.prod_apply]; exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
  · rfl

end X8GF

end X8part_b

section X8part_c
open scoped BigOperators Classical
open Matrix

namespace QAlgorithms.Papers.Independent.Support21.P11.X8G

open QAlgorithms.Papers.Independent.Renew46.P16 X8GF

variable {F : Type*} [Field F] (omega : ℕ → F) {r : ℕ} (u : Fin r → F)

abbrev MM := Matrix (Fin r) (Fin r) F

def gen : BMWLetter 2 → MM (F := F) (r := r)
  | .s _ => Sm u
  | .e _ => Em u
  | .x i => if i.val = 0 then Xm u else -Xm u

def ρ0 : FreeAlgebra F (BMWLetter 2) →ₐ[F] MM (F := F) (r := r) := FreeAlgebra.lift F (gen u)

lemma ρ0S : ρ0 u (freeS F 2 0) = Sm u := by
  simp [ρ0, freeS, gen]
lemma ρ0E : ρ0 u (freeE F 2 0) = Em u := by
  simp [ρ0, freeE, gen]
lemma ρ0X : ρ0 u (freeX F 2 0) = Xm u := by
  simp [ρ0, freeX, gen]
lemma ρ0Y : ρ0 u (freeX F 2 1) = -Xm u := by
  simp [ρ0, freeX, gen]

variable {omega u}

lemma ρ0_rel (hd : Function.Injective u) (hs : ∀ i j, u i + u j ≠ 0)
    (hw : ∀ a, omega a = ∑ i, gam u i * u i ^ a) ⦃a b : FreeAlgebra F (BMWLetter 2)⦄
    (h : BMWRel F omega 2 a b) : ρ0 u a = ρ0 u b := by
  cases h with
  | involution i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_pow, map_one, ρ0S, sq, SS hd hs]
  | braidFar i j hi hj hd => omega
  | braidNear i hi => omega
  | sx i j hi hj h1 h2 => omega
  | idempotent i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_pow, map_mul, AlgHom.commutes, ρ0E, sq, ← Algebra.smul_def]
    have := EXE (u := u) 0
    rw [pow_zero, mul_one] at this
    rw [this, hw 0]
  | seFar i j hi hj hd => omega
  | eeFar i j hi hj hd => omega
  | ex i j hi hj h1 h2 => omega
  | xxCommute i j hi hj =>
    interval_cases i <;> interval_cases j <;>
      simp only [map_mul, ρ0X, ρ0Y, mul_neg, neg_mul]
  | skeinLeft i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_sub, map_sub, map_mul, map_mul, map_one, ρ0S, ρ0E, ρ0X, zero_add, ρ0Y, neg_mul,
      sub_neg_eq_add, SX hs]
  | skeinRight i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_sub, map_sub, map_mul, map_mul, map_one, ρ0S, ρ0E, ρ0X, zero_add, ρ0Y, mul_neg,
      sub_neg_eq_add, add_comm, SX hs]
  | unwrap a ha hn =>
    rw [map_mul, map_mul, map_pow, map_mul, AlgHom.commutes, ρ0E, ρ0X, EXE, hw a,
      Algebra.smul_def]
  | es i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_mul, ρ0S, ρ0E, ES hd hs]
  | se i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_mul, ρ0S, ρ0E, SE hd hs]
  | tangleLeft i hi => omega
  | tangleRight i hi => omega
  | tangleLeftReverse i hi => omega
  | tangleRightReverse i hi => omega
  | untwistLeft i hi => omega
  | untwistRight i hi => omega
  | antisymLeft i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_mul, map_add, map_zero, ρ0E, ρ0X, zero_add, ρ0Y, add_neg_cancel, mul_zero]
  | antisymRight i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_mul, map_add, map_zero, ρ0E, ρ0X, zero_add, ρ0Y, add_neg_cancel, zero_mul]

variable (hd : Function.Injective u) (hs : ∀ i j, u i + u j ≠ 0)
  (hw : ∀ a, omega a = ∑ i, gam u i * u i ^ a)

def ρ1 : AffineBMW F omega 2 →ₐ[F] MM (F := F) (r := r) :=
  RingQuot.liftAlgHom F ⟨ρ0 u, ρ0_rel hd hs hw⟩

lemma ρ1_apply (x : FreeAlgebra F (BMWLetter 2)) :
    ρ1 hd hs hw (affineBMWQuotientMap F omega 2 x) = ρ0 u x := by
  rw [ρ1, affineBMWQuotientMap, RingQuot.liftAlgHom_mkAlgHom_apply]

lemma ρ1_rel ⦃a b : AffineBMW F omega 2⦄ (h : cyclotomicRel F omega 2 r u a b) :
    ρ1 hd hs hw a = ρ1 hd hs hw b := by
  obtain ⟨rfl, rfl⟩ := h
  rw [map_zero, cyclotomicPolynomial, map_list_prod, List.map_ofFn]
  have : (⇑(ρ1 hd hs hw) ∘ fun j : Fin r => affineX F omega 2 0 - algebraMap F _ (u j)) =
      fun j => Xm u - algebraMap F (MM (F := F) (r := r)) (u j) := by
    funext j
    simp only [Function.comp_apply, map_sub, AlgHom.commutes]
    rw [affineX, ρ1_apply, ρ0X]
  rw [this, cyc]

def ρ2 : CyclotomicBMW F omega 2 r u →ₐ[F] MM (F := F) (r := r) :=
  RingQuot.liftAlgHom F ⟨ρ1 hd hs hw, ρ1_rel hd hs hw⟩

lemma ρ2_apply (x : FreeAlgebra F (BMWLetter 2)) :
    ρ2 hd hs hw (cyclotomicMap F omega 2 r u (affineBMWQuotientMap F omega 2 x)) = ρ0 u x := by
  rw [ρ2, cyclotomicMap, RingQuot.liftAlgHom_mkAlgHom_apply, ρ1_apply]

lemma ρ2X : ρ2 hd hs hw (cyclotomicX F omega 2 r u 0) = Xm u := by
  rw [cyclotomicX, affineX, ρ2_apply, ρ0X]

lemma ρ2E : ρ2 hd hs hw (cyclotomicE F omega 2 r u 0) = Em u := by
  rw [cyclotomicE, affineE, ρ2_apply, ρ0E]

end QAlgorithms.Papers.Independent.Support21.P11.X8G

end X8part_c

section X8part_d
open scoped BigOperators Classical
open Matrix

namespace QAlgorithms.Papers.Independent.Support21.P11.X8G

open QAlgorithms.Papers.Independent.Renew46.P16 X8GF

variable {F : Type*} [Field F] {omega : ℕ → F} {r : ℕ} {u : Fin r → F}

lemma Em_mulVec (w : Fin r → F) : Em u *ᵥ w = (∑ i, gam u i * w i) • (fun _ => (1 : F)) := by
  ext j
  simp [mulVec, dotProduct, Em]

theorem hasCyclic (hd : Function.Injective u) (hs : ∀ i j, u i + u j ≠ 0)
    (hw : ∀ a, omega a = ∑ i, gam u i * u i ^ a) (hne : ∃ a, omega a ≠ 0) (hr : 1 ≤ r) :
    HasCyclicModule F omega r u := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let ρ : CyclotomicBMW F omega 2 r u →ₐ[F] Module.End F (Fin r → F) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) F ≃ₐ[F] _).toAlgHom.comp (ρ2 hd hs hw)
  have hρX : ∀ a : ℕ, ρ (cyclotomicX F omega 2 r u 0 ^ a) =
      Matrix.toLinAlgEquiv' (Xm u ^ a) := by
    intro a; simp only [ρ, map_pow, AlgHom.comp_apply, ρ2X]; rfl
  have hρE : ρ (cyclotomicE F omega 2 r u 0) = Matrix.toLin' (Em u) := by
    simp only [ρ, AlgHom.comp_apply, ρ2E]; rfl
  let fam : Fin r → (Fin r → F) := fun i k => u k ^ i.val
  have hli : LinearIndependent F fam := by
    have e : fam = fun i => (vandermonde u)ᵀ i := by
      funext i k; simp [fam, vandermonde_apply]
    rw [e]
    exact Matrix.linearIndependent_rows_of_det_ne_zero
      (by rw [det_transpose]; exact det_vandermonde_ne_zero_iff.mpr hd)
  let b : Module.Basis (Fin r) F (Fin r → F) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  refine ⟨ρ, fun _ => 1, b, ?_, ?_⟩
  · intro i
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    rw [← map_pow, hρX, Xm, diagonal_pow, Matrix.toLinAlgEquiv'_apply]
    ext k
    simp [fam, mulVec_diagonal]
  · rw [hρE]
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      rw [Matrix.toLin'_apply, Em_mulVec]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      obtain ⟨a, ha⟩ := hne
      have : ∃ i, gam u i ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact ha (by rw [hw a]; simp [hc])
      obtain ⟨i, hi⟩ := this
      refine ⟨Pi.single i (gam u i)⁻¹, ?_⟩
      rw [Matrix.toLin'_apply, Em_mulVec]
      simp [Pi.single_apply, hi]

theorem lc_of_hc (hr : 1 ≤ r) (h : HasCyclicModule F omega r u) :
    LinearIndependent F (idealFamily F omega r u) ∧ NonzeroCorner F omega r u := by
  obtain ⟨ρ, v, b, hb, hrange⟩ := h
  have hv : v ∈ LinearMap.range (ρ (cyclotomicE F omega 2 r u 0)) := by
    rw [hrange]; exact Submodule.mem_span_singleton_self v
  obtain ⟨w, hw⟩ := hv
  have key : ∀ (a : ℕ) (z : CyclotomicBMW F omega 2 r u),
      ρ (cyclotomicX F omega 2 r u 0 ^ a * z * cyclotomicE F omega 2 r u 0) w =
        (ρ (cyclotomicX F omega 2 r u 0) ^ a) (ρ z v) := by
    intro a z
    rw [map_mul, map_mul, map_pow, Module.End.mul_apply, Module.End.mul_apply, hw]
  constructor
  · refine (Fintype.linearIndependent_iff (v := idealFamily F omega r u)).mpr ?_
    intro g hg i
    have e : ∀ a : Fin r, ρ (idealFamily F omega r u a) w = b a := by
      intro a
      rw [idealFamily, map_mul, map_pow, Module.End.mul_apply, hw, hb a]
    have : ∑ a, g a • b a = 0 := by
      calc ∑ a, g a • b a = ρ (∑ a, g a • idealFamily F omega r u a) w := by
            rw [map_sum, LinearMap.sum_apply]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [map_smul, LinearMap.smul_apply, e]
        _ = 0 := by rw [hg, map_zero, LinearMap.zero_apply]
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent) g this i
  · intro hbot
    have h0 : ∀ a : Fin r, cyclotomicE F omega 2 r u 0 * cyclotomicX F omega 2 r u 0 ^ a.val *
        cyclotomicE F omega 2 r u 0 = 0 := by
      intro a
      have : cyclotomicE F omega 2 r u 0 * cyclotomicX F omega 2 r u 0 ^ a.val *
          cyclotomicE F omega 2 r u 0 ∈ cornerSpan F Set.univ (cyclotomicE F omega 2 r u 0) :=
        Submodule.subset_span ⟨_, Set.mem_univ _, rfl⟩
      rw [hbot] at this
      exact (Submodule.mem_bot F).mp this
    have hE : ρ (cyclotomicE F omega 2 r u 0) = 0 := by
      apply b.ext
      intro a
      rw [hb a, LinearMap.zero_apply, ← hw]
      have := congrArg (fun z => ρ z w) (h0 a)
      simp only [map_mul, map_pow, Module.End.mul_apply, map_zero, LinearMap.zero_apply] at this
      exact this
    rw [hE, LinearMap.range_zero, eq_comm, Submodule.span_singleton_eq_bot] at hrange
    have := b.ne_zero ⟨0, hr⟩
    rw [hb, pow_zero, Module.End.one_apply, hrange] at this
    exact this rfl

end QAlgorithms.Papers.Independent.Support21.P11.X8G

end X8part_d

section X8part_e
open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11.X8G

open QAlgorithms.Papers.Independent.Renew46.P16 X8GF

section Generic

variable {R : Type*} [CommRing R] {r : ℕ}

def Dx (u : Fin r → R) : R := ∏ i, ∏ j ∈ Finset.univ.erase i, (u i - u j)

def Lx (u : Fin r → R) (a : ℕ) : R :=
  ∑ i, 2 * (2 * u i - (-1 : R) ^ r) * (∏ j ∈ Finset.univ.erase i, (u i + u j)) *
    (∏ k ∈ Finset.univ.erase i, ∏ j ∈ Finset.univ.erase k, (u k - u j)) * u i ^ a

def Rx (u : Fin r → R) (a : ℕ) : R :=
  2 * Dx u * schurQ u (a + 1) - (-1 : R) ^ r * Dx u * schurQ u a + if a = 0 then Dx u else 0

lemma map_schurQList {R' : Type*} [CommRing R'] (f : R →+* R') (l : List R) (a : ℕ) :
    f (schurQList l a) = schurQList (l.map f) a := by
  induction l generalizing a with
  | nil => simp only [schurQList, List.map_nil]; split_ifs <;> simp
  | cons x l ih =>
    simp only [schurQList, List.map_cons, map_add, map_sum, map_mul, map_pow, map_ofNat, ih]

lemma map_schurQ {R' : Type*} [CommRing R'] (f : R →+* R') (u : Fin r → R) (a : ℕ) :
    f (schurQ u a) = schurQ (f ∘ u) a := by
  rw [schurQ, schurQ, map_schurQList, List.map_ofFn]

lemma map_Dx {R' : Type*} [CommRing R'] (f : R →+* R') (u : Fin r → R) :
    f (Dx u) = Dx (f ∘ u) := by
  simp [Dx, map_prod, map_sub]

lemma map_Lx {R' : Type*} [CommRing R'] (f : R →+* R') (u : Fin r → R) (a : ℕ) :
    f (Lx u a) = Lx (f ∘ u) a := by
  simp [Lx, map_sum, map_prod, map_sub, map_mul, map_pow, map_add, map_ofNat]

lemma map_Rx {R' : Type*} [CommRing R'] (f : R →+* R') (u : Fin r → R) (a : ℕ) :
    f (Rx u a) = Rx (f ∘ u) a := by
  simp only [Rx, map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat, map_Dx,
    map_schurQ]
  split_ifs <;> simp [map_Dx]

end Generic

section Fld

variable {L : Type*} [Field L] {r : ℕ}

lemma Dx_ne (u : Fin r → L) (hd : Function.Injective u) : Dx u ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj =>
    sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hj (hd h).symm

lemma Lx_eq (u : Fin r → L) (hd : Function.Injective u) (a : ℕ) :
    Lx u a = 2 * Dx u * ∑ i, weightGamma u i * u i ^ a := by
  rw [Lx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hden : ∏ j ∈ Finset.univ.erase i, (u i - u j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun h =>
      Finset.ne_of_mem_erase hj (hd h).symm
  have hD : Dx u = (∏ j ∈ Finset.univ.erase i, (u i - u j)) *
      ∏ k ∈ Finset.univ.erase i, ∏ j ∈ Finset.univ.erase k, (u k - u j) := by
    rw [Dx, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [hD, weightGamma, Finset.prod_div_distrib]
  field_simp

lemma Rx_eq (u : Fin r → L) (h2 : (2 : L) ≠ 0) (a : ℕ) :
    Rx u a = 2 * Dx u * schurEta u a := by
  rw [Rx, schurEta, Ring.inverse_eq_inv']
  split_ifs
  · field_simp; try ring
  · field_simp; try ring

end Fld

/-- Specialization of the generic identity (3.5) to a field. -/
theorem eta_eq {F : Type*} [Field F] {r : ℕ} (hr : 1 ≤ r) (u : Fin r → F) (h2 : (2 : F) ≠ 0)
    (hd : Function.Injective u) (a : ℕ) :
    schurEta u a = ∑ i, weightGamma u i * u i ^ a := by
  let P := MvPolynomial (Fin r) ℤ
  let K := FractionRing P
  let uK : Fin r → K := fun i => algebraMap P K (MvPolynomial.X i)
  have hinj : Function.Injective (algebraMap P K) := IsFractionRing.injective P K
  have huK : Function.Injective uK := fun i j h =>
    MvPolynomial.X_injective (hinj h)
  have h2K : (2 : K) ≠ 0 := by
    have : (2 : K) = algebraMap P K 2 := (map_ofNat _ 2).symm
    rw [this]
    refine hinj.ne_iff' (map_zero _) |>.mpr ?_
    intro h
    have h' : (MvPolynomial.C (2 : ℤ) : P) = MvPolynomial.C 0 := by
      rw [map_zero]; exact (map_ofNat MvPolynomial.C 2).trans h
    exact absurd (MvPolynomial.C_injective _ _ h') (by norm_num)
  have hid := (rational_weights_schur_identity r hr a).1
  have hK : Lx uK a = Rx uK a := by
    rw [Lx_eq uK huK, Rx_eq uK h2K]
    exact congrArg _ hid
  have hP : Lx (MvPolynomial.X : Fin r → P) a = Rx (MvPolynomial.X : Fin r → P) a := by
    apply hinj
    rw [map_Lx, map_Rx]
    exact hK
  have hF := congrArg (MvPolynomial.aeval (R := ℤ) u).toRingHom hP
  rw [map_Lx, map_Rx] at hF
  have hc : ((MvPolynomial.aeval (R := ℤ) u).toRingHom ∘ MvPolynomial.X) = u := by
    funext i; simp
  rw [hc, Lx_eq u hd, Rx_eq u h2] at hF
  have hne : (2 : F) * Dx u ≠ 0 := mul_ne_zero h2 (Dx_ne u hd)
  exact (mul_left_cancel₀ hne hF).symm

end QAlgorithms.Papers.Independent.Support21.P11.X8G

end X8part_e

section X8part_f
open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11.X8B

open QAlgorithms.Papers.Independent.Renew46.P16

variable (R : Type*) [CommRing R] (omega : ℕ → R) (r : ℕ) (u : Fin r → R)

abbrev W := CyclotomicBMW R omega 2 r u

def φ : FreeAlgebra R (BMWLetter 2) →ₐ[R] W R omega r u :=
  (cyclotomicMap R omega 2 r u).comp (affineBMWQuotientMap R omega 2)

abbrev S : W R omega r u := cyclotomicS R omega 2 r u 0
abbrev E : W R omega r u := cyclotomicE R omega 2 r u 0
abbrev X : W R omega r u := cyclotomicX R omega 2 r u 0
abbrev Y : W R omega r u := cyclotomicX R omega 2 r u 1

lemma φS : φ R omega r u (freeS R 2 0) = S R omega r u := rfl
lemma φE : φ R omega r u (freeE R 2 0) = E R omega r u := rfl
lemma φX : φ R omega r u (freeX R 2 0) = X R omega r u := rfl
lemma φY : φ R omega r u (freeX R 2 1) = Y R omega r u := rfl

lemma rel {a b : FreeAlgebra R (BMWLetter 2)} (h : BMWRel R omega 2 a b) :
    φ R omega r u a = φ R omega r u b := by
  simp only [φ, AlgHom.comp_apply]
  congr 1
  exact RingQuot.mkAlgHom_rel R h

variable {R omega r u}

lemma SS : S R omega r u * S R omega r u = 1 := by
  have := rel R omega r u (BMWRel.involution 0 (by norm_num))
  rw [map_pow, φS, map_one, sq] at this; exact this

lemma EE : E R omega r u * E R omega r u = omega 0 • E R omega r u := by
  have := rel R omega r u (BMWRel.idempotent 0 (by norm_num))
  rw [map_pow, φE, map_mul, AlgHom.commutes, sq, ← Algebra.smul_def] at this; exact this

lemma XY : X R omega r u * Y R omega r u = Y R omega r u * X R omega r u := by
  have := rel R omega r u (BMWRel.xxCommute 0 1 (by norm_num) (by norm_num))
  rw [map_mul, map_mul, φX, φY] at this; exact this

lemma skL : S R omega r u * X R omega r u -
    Y R omega r u * S R omega r u = E R omega r u - 1 := by
  have := rel R omega r u (BMWRel.skeinLeft 0 (by norm_num))
  rw [map_sub, map_sub, map_mul, map_mul, map_one, φS, φE, φX] at this
  have h1 : φ R omega r u (freeX R 2 (0 + 1)) = Y R omega r u := rfl
  rw [h1] at this
  exact this

lemma skR : X R omega r u * S R omega r u -
    S R omega r u * Y R omega r u = E R omega r u - 1 := by
  have := rel R omega r u (BMWRel.skeinRight 0 (by norm_num))
  rw [map_sub, map_sub, map_mul, map_mul, map_one, φS, φE, φX] at this
  have h1 : φ R omega r u (freeX R 2 (0 + 1)) = Y R omega r u := rfl
  rw [h1] at this
  exact this

lemma unwrap (a : ℕ) (ha : 0 < a) :
    E R omega r u * X R omega r u ^ a * E R omega r u = omega a • E R omega r u := by
  have := rel R omega r u (BMWRel.unwrap a ha le_rfl)
  simp only [map_mul, map_pow, AlgHom.commutes] at this
  rw [φE, φX] at this
  rw [this, Algebra.smul_def]

lemma ES : E R omega r u * S R omega r u = E R omega r u := by
  have := rel R omega r u (BMWRel.es 0 (by norm_num))
  rw [map_mul, φS, φE] at this; exact this

lemma SE : S R omega r u * E R omega r u = E R omega r u := by
  have := rel R omega r u (BMWRel.se 0 (by norm_num))
  rw [map_mul, φS, φE] at this; exact this

lemma EY : E R omega r u * (X R omega r u + Y R omega r u) = 0 := by
  have := rel R omega r u (BMWRel.antisymLeft 0 (by norm_num))
  rw [map_mul, map_add, map_zero, φE, φX] at this
  have h1 : φ R omega r u (freeX R 2 (0 + 1)) = Y R omega r u := rfl
  rw [h1] at this
  exact this

lemma YE : (X R omega r u + Y R omega r u) * E R omega r u = 0 := by
  have := rel R omega r u (BMWRel.antisymRight 0 (by norm_num))
  rw [map_mul, map_add, map_zero, φE, φX] at this
  have h1 : φ R omega r u (freeX R 2 (0 + 1)) = Y R omega r u := rfl
  rw [h1] at this
  exact this


lemma EXE' (a : ℕ) :
    E R omega r u * X R omega r u ^ a * E R omega r u = omega a • E R omega r u := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [pow_zero, mul_one, EE]
  · exact unwrap a ha

lemma absYb {A : Type*} [Ring A] (X Y E : A) (hXY : Commute X Y) (hY : (X + Y) * E = 0) (b : ℕ) :
    Y ^ b * E = (-X) ^ b * E := by
  have hY' : Y * E = (-X) * E := by
    rw [add_mul] at hY; rw [neg_mul]; exact eq_neg_of_add_eq_zero_right hY
  induction b with
  | zero => simp
  | succ b ih =>
    have hc : Commute (Y ^ b) (-X) := (Commute.pow_left hXY.symm b).neg_right
    rw [pow_succ, mul_assoc, hY', ← mul_assoc, hc.eq, mul_assoc, ih, ← mul_assoc, ← pow_succ']

lemma absCorner {A : Type*} [Ring A] (X Y E S : A) (hXY' : X * Y = Y * X) (hY : (X + Y) * E = 0)
    (hSE : S * E = E) (hz : ∀ n : ℕ, E * X ^ n * E = 0) (a b : ℕ) :
    E * (X ^ a * E * X ^ b) * E = 0 ∧ E * (X ^ a * Y ^ b * S) * E = 0 ∧
      E * (X ^ a * Y ^ b) * E = 0 := by
  have hXY : Commute X Y := hXY'
  have key : E * (X ^ a * Y ^ b) * E = 0 := by
    have : E * (X ^ a * Y ^ b) * E = E * X ^ a * ((-X) ^ b * E) := by
      rw [← absYb X Y E hXY hY b]; noncomm_ring
    rw [this]
    rcases Nat.even_or_odd b with hb | hb
    · rw [hb.neg_pow, ← mul_assoc, mul_assoc E, ← pow_add, hz]
    · rw [hb.neg_pow, neg_mul, mul_neg, ← mul_assoc, mul_assoc E, ← pow_add, hz, neg_zero]
  refine ⟨?_, ?_, key⟩
  · have : E * (X ^ a * E * X ^ b) * E = (E * X ^ a * E) * X ^ b * E := by noncomm_ring
    rw [this, hz, zero_mul, zero_mul]
  · have : E * (X ^ a * Y ^ b * S) * E = E * (X ^ a * Y ^ b) * (S * E) := by noncomm_ring
    rw [this, hSE, key]

theorem omega_ne (hr : 1 ≤ r) (hc : NonzeroCorner R omega r u) : ∃ a, omega a ≠ 0 := by
  by_contra h
  push_neg at h
  apply hc
  have hz : ∀ a, E R omega r u * X R omega r u ^ a * E R omega r u = 0 := by
    intro a; rw [EXE', h a, zero_smul]
  let φ : W R omega r u →ₗ[R] W R omega r u :=
    LinearMap.mulLeft R (E R omega r u) ∘ₗ LinearMap.mulRight R (E R omega r u)
  have hφ : ∀ y, φ y = E R omega r u * y * E R omega r u := by
    intro y; simp [φ, mul_assoc]
  have hfam : ∀ t, φ (algebraFamily R omega r u t) = 0 := by
    intro t
    rw [hφ]
    have hc := absCorner (X R omega r u) (Y R omega r u) (E R omega r u) (S R omega r u)
      (XY (R := R) (omega := omega) (r := r) (u := u)) YE SE hz t.2.1.val t.2.2.val
    simp only [algebraFamily]
    split_ifs
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2
  have htop := (two_strand_spanning R omega r u hr).2
  have hall : ∀ y, φ y = 0 := by
    intro y
    have hy : y ∈ Submodule.span R (Set.range (algebraFamily R omega r u)) := by
      rw [htop]; trivial
    have : Submodule.span R (Set.range (algebraFamily R omega r u)) ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]; rintro _ ⟨t, rfl⟩; exact hfam t
    exact this hy
  rw [cornerSpan, Submodule.span_eq_bot]
  rintro _ ⟨y, _, rfl⟩
  have := hall y; rw [hφ] at this; exact this

end QAlgorithms.Papers.Independent.Support21.P11.X8B

namespace QAlgorithms.Papers.Independent.Support21.P11.X8G

open QAlgorithms.Papers.Independent.Renew46.P16 X8GF

theorem x8_main (F : Type*) [Field F] (omega : ℕ → F)
    (r : ℕ) (u : Fin r → F) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (hdistinct : Function.Injective u) (hsum : ∀ i j : Fin r, u i + u j ≠ 0) :
    ((LinearIndependent F (idealFamily F omega r u) ∧ NonzeroCorner F omega r u) ↔
      ((∀ a : ℕ, omega a = ∑ i : Fin r, weightGamma u i * u i ^ a) ∧
        ∃ a : ℕ, omega a ≠ 0)) ∧
    (((∀ a : ℕ, omega a = ∑ i : Fin r, weightGamma u i * u i ^ a) ∧
        ∃ a : ℕ, omega a ≠ 0) ↔ HasCyclicModule F omega r u) := by
  have hg : ∀ i, gam u i = weightGamma u i := fun i => rfl
  have LF : LinearIndependent F (idealFamily F omega r u) ∧ NonzeroCorner F omega r u →
      ((∀ a : ℕ, omega a = ∑ i : Fin r, weightGamma u i * u i ^ a) ∧ ∃ a : ℕ, omega a ≠ 0) :=
    fun ⟨hli, hc⟩ => ⟨fun a => (generic_field_schur_formula F omega r u hr h2 hdistinct hsum hli hc a).trans
      (eta_eq hr u h2 hdistinct a), X8B.omega_ne hr hc⟩
  have FH : ((∀ a : ℕ, omega a = ∑ i : Fin r, weightGamma u i * u i ^ a) ∧ ∃ a : ℕ, omega a ≠ 0) →
      HasCyclicModule F omega r u :=
    fun ⟨hw, hne⟩ => hasCyclic hdistinct hsum (fun a => by simp only [hg]; exact hw a) hne hr
  exact ⟨⟨LF, fun h => lc_of_hc hr (FH h)⟩, ⟨FH, fun h => LF (lc_of_hc hr h)⟩⟩

end QAlgorithms.Papers.Independent.Support21.P11.X8G

open QAlgorithms.Papers.Independent.Support21.P11 QAlgorithms.Papers.Independent.Renew46.P16 in
theorem solution (F : Type*) [Field F] (omega : ℕ → F)
    (r : ℕ) (u : Fin r → F) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (hdistinct : Function.Injective u) (hsum : ∀ i j : Fin r, u i + u j ≠ 0) :
    ((LinearIndependent F (idealFamily F omega r u) ∧ NonzeroCorner F omega r u) ↔
      ((∀ a : ℕ, omega a = ∑ i : Fin r, weightGamma u i * u i ^ a) ∧
        ∃ a : ℕ, omega a ≠ 0)) ∧
    (((∀ a : ℕ, omega a = ∑ i : Fin r, weightGamma u i * u i ^ a) ∧
        ∃ a : ℕ, omega a ≠ 0) ↔ HasCyclicModule F omega r u) :=
  QAlgorithms.Papers.Independent.Support21.P11.X8G.x8_main F omega r u hr h2 hdistinct hsum

end X8part_f
