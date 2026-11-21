-- Prove2me | solution 1 for TranspositionIID.Main.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T18:04:16.243947+00:00
-- url     : https://prove2.me/submissions/9498313f-016e-42dc-9f83-8ae7f89670e3

import Mathlib
import Definitions.Def_TranspositionIID_Main_Exclusion

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
/-!
Blueprint for Lemma 3.2 (biased exclusion inversion count), elementary route.

Instead of Levin–Peres, the mixing step uses:
* the grand coupling (same edge, same bit) is monotone for the prefix-H-count order `wle`;
* with `ρ = exp (-θ)`, the functions `ρ ^ pre z j` evolve linearly under the kernel (`kernel_rho`);
* a weighted sum with weights `exp(θ j/2) j (N-j)` contracts by `1 - 4/(N^2 (N-1))` per step.
-/
/-- Number of `true` (H) letters among positions `< j`. -/
def pre (w : BinaryWord N) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => i.val < j ∧ w i = true)).card

/-- Number of H letters. -/
def hcount (w : BinaryWord N) : ℕ := (Finset.univ.filter (fun i : Fin N => w i = true)).card

/-- The prefix order: `w` is everywhere less sorted than `z`. -/
def wle (w z : BinaryWord N) : Prop := ∀ j, pre w j ≤ pre z j

/-- Monotone (increasing in the prefix order) observable. -/
def MonoW (f : BinaryWord N → ℝ) : Prop := ∀ w z, wle w z → f w ≤ f z

/-- H-first probability. -/
noncomputable def qH (θ : ℝ) : ℝ := 1 / (1 + Real.exp (-θ))

/-- The least sorted word with `h` letters H: L^(N-h) H^h. -/
def bot (N h : ℕ) : BinaryWord N := fun i => decide (N - h ≤ i.val)

/-- Unnormalized stationary weight on the class `hcount = h`. -/
noncomputable def zw (θ : ℝ) (h : ℕ) (z : BinaryWord N) : ℝ :=
  if hcount z = h then Real.exp (-θ * binaryInversions z) else 0

/-- Stationary law on the class `hcount = h`. -/
noncomputable def zeta (θ : ℝ) (h : ℕ) (z : BinaryWord N) : ℝ :=
  zw θ h z / ∑ y : BinaryWord N, zw θ h y

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartD
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
/-! ### Counting helpers -/
/-- H-count as a sum. -/
def hc {m : ℕ} (w : Fin m → Bool) : ℕ := ∑ i, if w i = true then 1 else 0

/-- Inversion count as a natural double sum. -/
def inv {m : ℕ} (w : Fin m → Bool) : ℕ :=
  ∑ i, ∑ j, if i < j ∧ w i = false ∧ w j = true then 1 else 0

lemma hcount_eq_hc (w : BinaryWord N) : hcount w = hc w := by
  unfold hcount hc; rw [Finset.card_filter]

lemma binaryInversions_eq_inv (w : BinaryWord N) : binaryInversions w = (inv w : ℝ) := by
  unfold binaryInversions inv
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]

lemma zw_nonneg (θ : ℝ) (h : ℕ) (z : BinaryWord N) : 0 ≤ zw θ h z := by
  unfold zw; split_ifs <;> positivity

lemma exists_class (h : ℕ) (hh : h ≤ N) : ∃ w : BinaryWord N, hcount w = h := by
  refine ⟨fun i => decide (i.val < h), ?_⟩
  unfold hcount
  have : (Finset.univ.filter (fun i : Fin N => decide (i.val < h) = true)).map Fin.valEmbedding
      = Finset.range h := by
    ext x; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq, Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map, this, Finset.card_range]

lemma denom_pos (θ : ℝ) (h : ℕ) (hh : h ≤ N) : 0 < ∑ y : BinaryWord N, zw θ h y := by
  obtain ⟨w, hw⟩ := exists_class h hh
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun y _ => zw_nonneg θ h y) (Finset.mem_univ w))
  unfold zw; rw [if_pos hw]; positivity

theorem zeta_nonneg (θ : ℝ) (h : ℕ) (z : BinaryWord N) : 0 ≤ zeta θ h z := by
  unfold zeta
  exact div_nonneg (zw_nonneg θ h z) (Finset.sum_nonneg fun y _ => zw_nonneg θ h y)

end TranspositionIID.Main.Dev.L32.PartD
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
alias zeta_nonneg := TranspositionIID.Main.Dev.L32.PartD.zeta_nonneg

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartD
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
theorem zeta_sum (θ : ℝ) (h : ℕ) (hh : h ≤ N) : ∑ z : BinaryWord N, zeta θ h z = 1 := by
  unfold zeta
  rw [← Finset.sum_div, div_self (denom_pos θ h hh).ne']

end TranspositionIID.Main.Dev.L32.PartD
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
alias zeta_sum := TranspositionIID.Main.Dev.L32.PartD.zeta_sum

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartD
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
theorem zeta_class (θ : ℝ) (h : ℕ) (z : BinaryWord N) (hz : zeta θ h z ≠ 0) : hcount z = h := by
  unfold zeta zw at hz
  by_contra hc'
  rw [if_neg hc'] at hz
  simp at hz

end TranspositionIID.Main.Dev.L32.PartD
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartD
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
variable (k : Fin (N - 1))
/-! ### Detailed balance -/
/-- The two sites of edge `k`. -/
def i0 : Fin N := ⟨k.val, by omega⟩

def i1 : Fin N := ⟨k.val + 1, by omega⟩

lemma i0_ne_i1 : i0 k ≠ i1 k := by
  simp [i0, i1, Fin.ext_iff]

/-- The adjacent transposition. -/
def sw : Equiv.Perm (Fin N) := Equiv.swap (i0 k) (i1 k)

lemma update_eq (a : BinaryWord N) (b : Bool) :
    exclusionUpdate a k b = if a (i0 k) = a (i1 k) ∨ b = a (i0 k) then a else a ∘ sw k := by
  unfold exclusionUpdate
  change (if a (i0 k) = a (i1 k) then a else fun i => if i = i0 k then b else
    if i = i1 k then !b else a i) = _
  have hne := i0_ne_i1 k
  by_cases h1 : a (i0 k) = a (i1 k)
  · simp [h1]
  · by_cases h2 : b = a (i0 k)
    · simp only [h1, h2, if_false, or_true, if_true]
      funext i
      by_cases hi0 : i = i0 k
      · subst hi0; simp
      · by_cases hi1 : i = i1 k
        · subst hi1; simp only [hi0, if_false, if_true]
          cases ha : a (i0 k) <;> cases hb : a (i1 k) <;> simp_all
        · simp [hi0, hi1]
    · simp only [h1, h2, or_self, if_false]
      funext i
      simp only [Function.comp, sw, Equiv.swap_apply_def]
      by_cases hi0 : i = i0 k
      · subst hi0; simp only [if_true]
        cases ha : a (i0 k) <;> cases hb : a (i1 k) <;> cases b <;> simp_all
      · by_cases hi1 : i = i1 k
        · subst hi1; simp only [hi0, if_false, if_true]
          cases ha : a (i0 k) <;> cases hb : a (i1 k) <;> cases b <;> simp_all
        · simp [hi0, hi1]

lemma sw_sw (a : BinaryWord N) : (a ∘ sw k) ∘ sw k = a := by
  funext i; simp [sw, Function.comp]

lemma hc_sw (a : BinaryWord N) : hc (a ∘ sw k) = hc a := by
  unfold hc
  exact Equiv.sum_comp (sw k) (fun i => if a i = true then 1 else 0)

lemma sw_lt_iff (u v : Fin N) (h : ¬ (u = i0 k ∧ v = i1 k)) (h' : ¬ (u = i1 k ∧ v = i0 k)) :
    sw k u < sw k v ↔ u < v := by
  simp only [sw, Equiv.swap_apply_def, i0, i1, Fin.ext_iff, Fin.lt_def] at *
  split_ifs <;> simp_all <;> omega

lemma inv_pairs {m : ℕ} (w : Fin m → Bool) :
    inv w = ∑ p : Fin m × Fin m, if p.1 < p.2 ∧ w p.1 = false ∧ w p.2 = true then 1 else 0 := by
  rw [Fintype.sum_prod_type]; rfl

lemma inv_sw (a : BinaryWord N) (h0 : a (i0 k) = false) (h1 : a (i1 k) = true) :
    inv (a ∘ sw k) + 1 = inv a := by
  rw [inv_pairs, inv_pairs]
  set f : Fin N × Fin N → ℕ := fun p =>
    if sw k p.1 < sw k p.2 ∧ a p.1 = false ∧ a p.2 = true then 1 else 0
  have e1 : (∑ x : Fin N × Fin N,
      (if x.1 < x.2 ∧ (a ∘ sw k) x.1 = false ∧ (a ∘ sw k) x.2 = true then 1 else 0 : ℕ))
      = ∑ x, f x := by
    refine Fintype.sum_equiv ((sw k).prodCongr (sw k)) _ _ (fun p => ?_)
    simp only [f, Function.comp, Equiv.prodCongr_apply, Prod.map]
    simp only [sw, Equiv.swap_apply_self]
    exact if_congr Iff.rfl rfl rfl
  rw [e1]
  have hne := i0_ne_i1 k
  have hlt : i0 k < i1 k := by simp [i0, i1, Fin.lt_def]
  have hs0 : sw k (i0 k) = i1 k := by simp [sw]
  have hs1 : sw k (i1 k) = i0 k := by simp [sw]
  have pt : ∀ p : Fin N × Fin N, f p + (if p = (i0 k, i1 k) then 1 else 0) =
      (if p.1 < p.2 ∧ a p.1 = false ∧ a p.2 = true then 1 else 0) := by
    intro p
    by_cases hp1 : p = (i0 k, i1 k)
    · subst hp1; simp [f, hs0, hs1, h0, h1, hlt, not_lt.2 hlt.le]
    · by_cases hp2 : p = (i1 k, i0 k)
      · subst hp2; simp [f, hs0, hs1, h0, h1, hlt, not_lt.2 hlt.le]
        intro h; exact absurd h.symm hne
      · simp only [f, if_neg hp1, add_zero]
        simp only [sw_lt_iff k p.1 p.2 (fun h => hp1 (Prod.ext h.1 h.2))
          (fun h => hp2 (Prod.ext h.1 h.2))]
  rw [← Finset.sum_congr rfl (fun p _ => pt p), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma sw_fix (a : BinaryWord N) (h : a (i0 k) = a (i1 k)) : a ∘ sw k = a := by
  funext i
  simp only [Function.comp, sw, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

/-- One edge's contribution to the kernel. -/
noncomputable def T (θ : ℝ) (a z : BinaryWord N) : ℝ :=
  (if exclusionUpdate a k true = z then 1 / (1 + Real.exp (-θ)) else 0) +
    (if exclusionUpdate a k false = z then 1 - 1 / (1 + Real.exp (-θ)) else 0)

lemma T_zero (θ : ℝ) (a z : BinaryWord N) (h1 : a ≠ z) (h2 : a ∘ sw k ≠ z) : T k θ a z = 0 := by
  unfold T; rw [update_eq, update_eq]
  split_ifs <;> simp_all

lemma zw_sw (θ : ℝ) (h : ℕ) (a : BinaryWord N) (h0 : a (i0 k) = false)
    (h1 : a (i1 k) = true) : zw θ h a = zw θ h (a ∘ sw k) * Real.exp (-θ) := by
  have hi := inv_sw k a h0 h1
  unfold zw
  rw [hcount_eq_hc, hcount_eq_hc, hc_sw, binaryInversions_eq_inv, binaryInversions_eq_inv, ← hi]
  split_ifs
  · rw [← Real.exp_add]; congr 1; push_cast; ring
  · simp

lemma db_key (θ : ℝ) (h : ℕ) (a : BinaryWord N) (h0 : a (i0 k) = false)
    (h1 : a (i1 k) = true) :
    zw θ h a * T k θ a (a ∘ sw k) = zw θ h (a ∘ sw k) * T k θ (a ∘ sw k) a := by
  have hne : a ≠ a ∘ sw k := by
    intro e; have := congrFun e (i0 k)
    simp [sw, h0, h1] at this
  have hT1 : T k θ a (a ∘ sw k) = 1 / (1 + Real.exp (-θ)) := by
    unfold T; rw [update_eq, update_eq]; simp [h0, h1, hne]
  have hT2 : T k θ (a ∘ sw k) a = 1 - 1 / (1 + Real.exp (-θ)) := by
    unfold T; rw [update_eq, update_eq, sw_sw]
    have e0 : (a ∘ sw k) (i0 k) = true := by simp [sw, h1]
    have e1 : (a ∘ sw k) (i1 k) = false := by simp [sw, h0]
    simp only [Function.comp] at e0 e1
    simp [e0, e1, Ne.symm hne]
  rw [hT1, hT2, zw_sw k θ h a h0 h1]
  have hp : 0 < Real.exp (-θ) := Real.exp_pos _
  field_simp
  ring

lemma db_term (θ : ℝ) (h : ℕ) (a z : BinaryWord N) :
    zw θ h a * T k θ a z = zw θ h z * T k θ z a := by
  by_cases e : a = z
  · subst e; rfl
  by_cases e2 : a ∘ sw k = z
  · subst e2
    have hd : a (i0 k) ≠ a (i1 k) := fun hh => e (sw_fix k a hh).symm
    cases h0 : a (i0 k) <;> cases h1 : a (i1 k) <;> rw [h0, h1] at hd
    · exact absurd rfl hd
    · exact db_key k θ h a h0 h1
    · have e0 : (a ∘ sw k) (i0 k) = false := by simp [sw, h1]
      have e1 : (a ∘ sw k) (i1 k) = true := by simp [sw, h0]
      have := db_key k θ h (a ∘ sw k) e0 e1
      rw [sw_sw] at this
      exact this.symm
    · exact absurd rfl hd
  · rw [T_zero k θ a z e e2, T_zero k θ z a (Ne.symm e)]
    · simp
    · intro e3; apply e2; rw [← e3, sw_sw]

end TranspositionIID.Main.Dev.L32.PartD
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartD
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
/-! ### Stationarity -/
lemma kernel_eq (θ : ℝ) (a z : BinaryWord N) :
    exclusionKernel N θ a z = ∑ k : Fin (N - 1), T k θ a z / ((N - 1 : ℕ) : ℝ) := rfl

lemma db_zw (θ : ℝ) (h : ℕ) (a z : BinaryWord N) :
    zw θ h a * exclusionKernel N θ a z = zw θ h z * exclusionKernel N θ z a := by
  rw [kernel_eq, kernel_eq, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mul_div_assoc', mul_div_assoc', db_term k θ h a z]

lemma row_sum (hN : 2 ≤ N) (θ : ℝ) (w : BinaryWord N) :
    ∑ z, exclusionKernel N θ w z = 1 := by
  simp only [kernel_eq]
  rw [Finset.sum_comm]
  have hT : ∀ k : Fin (N - 1), ∑ z, T k θ w z / ((N - 1 : ℕ) : ℝ) = 1 / ((N - 1 : ℕ) : ℝ) := by
    intro k
    rw [← Finset.sum_div]
    unfold T
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun k _ => hT k), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 1 ≤ N - 1 := by omega
    exact_mod_cast (by omega : N - 1 ≠ 0)
  field_simp

lemma zeta_vecMul (hN : 2 ≤ N) (θ : ℝ) (h : ℕ) :
    Matrix.vecMul (fun a => zeta θ h a) (exclusionKernel N θ) = fun a => zeta θ h a := by
  funext z
  simp only [Matrix.vecMul, dotProduct, zeta]
  have : ∀ a, zw θ h a / (∑ y : BinaryWord N, zw θ h y) * exclusionKernel N θ a z =
      zw θ h z / (∑ y : BinaryWord N, zw θ h y) * exclusionKernel N θ z a := by
    intro a
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, db_zw]
  rw [Finset.sum_congr rfl (fun a _ => this a), ← Finset.mul_sum, row_sum hN, mul_one]

lemma zeta_vecMul_pow (hN : 2 ≤ N) (θ : ℝ) (h : ℕ) (t : ℕ) :
    Matrix.vecMul (fun a => zeta θ h a) (exclusionKernel N θ ^ t) = fun a => zeta θ h a := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, zeta_vecMul hN]

theorem zeta_stationary (hN : 2 ≤ N) (θ : ℝ) (h : ℕ) (hh : h ≤ N) (t : ℕ)
    (f : BinaryWord N → ℝ) :
    ∑ a, zeta θ h a * expectedAfter (exclusionKernel N θ) a t f = ∑ a, zeta θ h a * f a := by
  have := Matrix.dotProduct_mulVec (fun a => zeta θ h a) (exclusionKernel N θ ^ t) f
  rw [zeta_vecMul_pow hN] at this
  exact this

end TranspositionIID.Main.Dev.L32.PartD
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
/-! ### Part D: the stationary law -/
alias zeta_stationary := TranspositionIID.Main.Dev.L32.PartD.zeta_stationary

alias zeta_class := TranspositionIID.Main.Dev.L32.PartD.zeta_class

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartD
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
/-! ### The analytic bound -/
/-- The partial sums `S_h = ∑_{i=1}^h i q^i/(1-q^i)`. -/
noncomputable def S (q : ℝ) (h : ℕ) : ℝ :=
  ∑ i ∈ Finset.range h, ((i : ℝ) + 1) * q ^ (i + 1) / (1 - q ^ (i + 1))

lemma S_nonneg (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (h : ℕ) : 0 ≤ S q h := by
  unfold S
  refine Finset.sum_nonneg fun i _ => div_nonneg (by positivity) ?_
  have : q ^ (i + 1) < 1 := pow_lt_one₀ hq0 hq1 (by omega)
  linarith

lemma geom_term_bound (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 ≤ 1 / x ^ 2 := by
  set e := Real.exp (-(x / 2)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hp : Real.exp (-x) = e ^ 2 := by
    rw [he, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hinv : Real.exp (x / 2) = 1 / e := by
    rw [he, Real.exp_neg]; field_simp
  have hs := Real.self_le_sinh_iff.2 (by linarith : 0 ≤ x / 2)
  rw [Real.sinh_eq, hinv, ← he] at hs
  -- hs : x / 2 ≤ (1/e - e) / 2
  have hu : x ≤ 1 / e - e := by linarith
  have h1 : 1 - e ^ 2 = e * (1 / e - e) := by field_simp
  have hlt : e ^ 2 < 1 := by
    rw [← hp]; exact Real.exp_lt_one_iff.2 (by linarith)
  rw [hp, div_le_div_iff₀ (by nlinarith) (by positivity), h1]
  have : x ^ 2 ≤ (1 / e - e) ^ 2 := pow_le_pow_left₀ hx.le hu 2
  nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt (pow_pos he0 2))]

lemma partial_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (h : ℕ) :
    ∑ i ∈ Finset.range h, ((i : ℝ) + 1) * p ^ (i + 1) ≤ p / (1 - p) ^ 2 := by
  have hs := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := p)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hp0]; exact hp1)
  have := sum_le_hasSum (Finset.range (h + 1)) (fun i _ => by positivity) hs
  rw [Finset.sum_range_succ'] at this
  simpa using this

theorem S_le (θ : ℝ) (hθ : 0 < θ) (h : ℕ) :
    S (Real.exp (-θ)) h ≤ Real.pi ^ 2 / (6 * θ ^ 2) := by
  set q := Real.exp (-θ) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hterm : ∀ i ∈ Finset.range h, HasSum (fun n : ℕ => ((i : ℝ) + 1) * (q ^ (i + 1)) ^ (n + 1))
      (((i : ℝ) + 1) * q ^ (i + 1) / (1 - q ^ (i + 1))) := by
    intro i _
    have r1 : q ^ (i + 1) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
    have := (hasSum_geometric_of_lt_one (by positivity : 0 ≤ q ^ (i + 1)) r1).mul_left
      (((i : ℝ) + 1) * q ^ (i + 1))
    have hf : (fun n : ℕ => ((i : ℝ) + 1) * (q ^ (i + 1)) ^ (n + 1)) =
        fun n => ((i : ℝ) + 1) * q ^ (i + 1) * (q ^ (i + 1)) ^ n := by
      funext n; ring
    rw [hf, div_eq_mul_inv]; exact this
  have hS := hasSum_sum hterm
  have hz : HasSum (fun n : ℕ => 1 / θ ^ 2 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2))
      (1 / θ ^ 2 * (Real.pi ^ 2 / 6)) := by
    refine HasSum.mul_left _ ?_
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).2 hasSum_zeta_two
    simpa using this
  have hle := hasSum_le (fun n => ?_) hS hz
  · unfold S
    calc _ ≤ 1 / θ ^ 2 * (Real.pi ^ 2 / 6) := hle
      _ = _ := by field_simp
  · -- pointwise bound
    set p := q ^ (n + 1) with hpdef
    have hp0 : 0 ≤ p := by positivity
    have hp1 : p < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
    have e : ∀ i : ℕ, ((i : ℝ) + 1) * (q ^ (i + 1)) ^ (n + 1) = ((i : ℝ) + 1) * p ^ (i + 1) := by
      intro i; rw [hpdef, ← pow_mul, ← pow_mul, Nat.mul_comm (n + 1)]
    simp only [e]
    refine (partial_bound p hp0 hp1 h).trans ?_
    have hx : 0 < θ * ((n : ℝ) + 1) := by positivity
    have hpe : p = Real.exp (-(θ * ((n : ℝ) + 1))) := by
      rw [hpdef, hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hpe]
    refine (geom_term_bound _ hx).trans (le_of_eq ?_)
    push_cast
    field_simp

/-! ### First- and last-letter decompositions -/
/-- L-count. -/
def lc {m : ℕ} (w : Fin m → Bool) : ℕ := ∑ i, if w i = false then 1 else 0

lemma hc_add_lc {m : ℕ} (w : Fin m → Bool) : hc w + lc w = m := by
  unfold hc lc
  rw [← Finset.sum_add_distrib]
  have : ∀ i, ((if w i = true then 1 else 0) + if w i = false then 1 else 0 : ℕ) = 1 := by
    intro i; cases w i <;> simp
  simp [this]

lemma hc_cons {m : ℕ} (b : Bool) (w : Fin m → Bool) :
    hc (Fin.cons b w : Fin (m + 1) → Bool) = hc w + if b = true then 1 else 0 := by
  unfold hc; rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; ring

lemma inv_cons {m : ℕ} (b : Bool) (w : Fin m → Bool) :
    inv (Fin.cons b w : Fin (m + 1) → Bool) = (if b = false then hc w else 0) + inv w := by
  unfold inv hc
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, false_and,
    if_false, zero_add, Fin.succ_pos, true_and, Fin.succ_lt_succ_iff, Fin.not_lt_zero]
  cases b <;> simp

lemma hc_snoc {m : ℕ} (b : Bool) (w : Fin m → Bool) :
    hc (Fin.snoc w b : Fin (m + 1) → Bool) = hc w + if b = true then 1 else 0 := by
  unfold hc; rw [Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc, Fin.snoc_last]

lemma inv_snoc {m : ℕ} (b : Bool) (w : Fin m → Bool) :
    inv (Fin.snoc w b : Fin (m + 1) → Bool) = inv w + (if b = true then lc w else 0) := by
  unfold inv lc
  have hl : ∀ x : Fin m, ¬ Fin.last m < x.castSucc := fun x => not_lt.2 (Fin.castSucc_lt_last x).le
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, lt_self_iff_false,
    false_and, if_false, add_zero, Fin.castSucc_lt_last, true_and, Fin.castSucc_lt_castSucc_iff,
    hl]
  rw [Finset.sum_add_distrib]
  cases b <;> simp

lemma sum_cons {m : ℕ} (G : (Fin (m + 1) → Bool) → ℝ) :
    ∑ w, G w = ∑ w : Fin m → Bool, G (Fin.cons false w) + ∑ w : Fin m → Bool, G (Fin.cons true w) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rfl

lemma sum_snoc {m : ℕ} (G : (Fin (m + 1) → Bool) → ℝ) :
    ∑ w, G w = ∑ w : Fin m → Bool, G (Fin.snoc w false) + ∑ w : Fin m → Bool, G (Fin.snoc w true) := by
  rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rfl

/-! ### Partition functions -/
noncomputable def Z (q : ℝ) (m h : ℕ) : ℝ :=
  ∑ w : Fin m → Bool, if hc w = h then q ^ inv w else 0

noncomputable def W (q : ℝ) (m h : ℕ) : ℝ :=
  ∑ w : Fin m → Bool, if hc w = h then q ^ inv w * (inv w : ℝ) else 0

lemma Z_nonneg (q : ℝ) (hq : 0 ≤ q) (m h : ℕ) : 0 ≤ Z q m h := by
  unfold Z; exact Finset.sum_nonneg fun w _ => by split_ifs <;> positivity

lemma W_zero (q : ℝ) (h : ℕ) : W q 0 h = 0 := by
  simp [W, inv]

lemma Z_cons (q : ℝ) (m h : ℕ) : Z q (m + 1) (h + 1) = q ^ (h + 1) * Z q m (h + 1) + Z q m h := by
  unfold Z; rw [sum_cons]; simp only [hc_cons, inv_cons]
  simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, add_zero, zero_add,
    Nat.add_right_cancel_iff]
  rw [Finset.mul_sum]; congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs with hw <;> simp [hw, pow_add]

lemma Z_cons0 (q : ℝ) (m : ℕ) : Z q (m + 1) 0 = Z q m 0 := by
  unfold Z; rw [sum_cons]; simp only [hc_cons, inv_cons]
  simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, add_zero, Nat.add_one_ne_zero]
  simp only [Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs with hw <;> simp [hw]

lemma W_cons (q : ℝ) (m h : ℕ) : W q (m + 1) (h + 1) =
    q ^ (h + 1) * (((h : ℝ) + 1) * Z q m (h + 1) + W q m (h + 1)) + W q m h := by
  have e1 : (∑ w : Fin m → Bool, if hc w = h + 1 then
      q ^ (hc w + inv w) * ((hc w + inv w : ℕ) : ℝ) else 0) =
      q ^ (h + 1) * (((h : ℝ) + 1) * Z q m (h + 1) + W q m (h + 1)) := by
    unfold Z W
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs with hw
    · rw [hw, pow_add]; push_cast; ring
    · simp
  rw [← e1]
  unfold W; rw [sum_cons]; simp only [hc_cons, inv_cons]
  simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, add_zero, zero_add,
    Nat.add_right_cancel_iff]

lemma W_cons0 (q : ℝ) (m : ℕ) : W q (m + 1) 0 = W q m 0 := by
  unfold W; rw [sum_cons]; simp only [hc_cons, inv_cons]
  simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, add_zero, Nat.add_one_ne_zero]
  simp only [Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs with hw <;> simp [hw]

lemma Z_snoc (q : ℝ) (m h : ℕ) : Z q (m + 1) (h + 1) = Z q m (h + 1) + q ^ (m - h) * Z q m h := by
  unfold Z; rw [sum_snoc]; simp only [hc_snoc, inv_snoc]
  simp only [Bool.false_eq_true, if_false, if_true, add_zero,
    Nat.add_right_cancel_iff]
  rw [Finset.mul_sum]; congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs with hw
  · have := hc_add_lc w
    have hl : lc w = m - h := by omega
    rw [hl, pow_add, mul_comm]
  · simp

lemma Z_rel (q : ℝ) (hq0 : 0 ≤ q) (m h : ℕ) :
    (1 - q ^ (h + 1)) * Z q m (h + 1) ≤ Z q m h := by
  have h1 := Z_cons q m h
  have h2 := Z_snoc q m h
  have : 0 ≤ q ^ (m - h) * Z q m h := mul_nonneg (by positivity) (Z_nonneg q hq0 m h)
  nlinarith

lemma W_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    ∀ h, W q m h ≤ S q h * Z q m h := by
  induction m with
  | zero => intro h; rw [W_zero]; exact mul_nonneg (S_nonneg q hq0 hq1 h) (Z_nonneg q hq0 0 h)
  | succ m ih =>
    intro h
    cases h with
    | zero => rw [W_cons0, Z_cons0]; exact ih 0
    | succ h =>
      rw [W_cons, Z_cons]
      set r := q ^ (h + 1) with hr
      have r0 : 0 ≤ r := by positivity
      have r1 : r < 1 := pow_lt_one₀ hq0 hq1 (by omega)
      set c := ((h : ℝ) + 1) * r / (1 - r) with hc'
      have hS : S q (h + 1) = S q h + c := by
        rw [S, Finset.sum_range_succ]; rfl
      have hc0 : 0 ≤ c := div_nonneg (by positivity) (by linarith)
      have hcr : c * (1 - r) = ((h : ℝ) + 1) * r := by
        rw [hc']; field_simp [(by linarith : (1 - r) ≠ 0)]
      have hrel := Z_rel q hq0 m h
      rw [← hr] at hrel
      have k1 : c * ((1 - r) * Z q m (h + 1)) ≤ c * Z q m h := mul_le_mul_of_nonneg_left hrel hc0
      have k2 : r * W q m (h + 1) ≤ r * (S q (h + 1) * Z q m (h + 1)) :=
        mul_le_mul_of_nonneg_left (ih (h + 1)) r0
      have k3 := ih h
      rw [hS] at k2 ⊢
      have k1' : ((h : ℝ) + 1) * r * Z q m (h + 1) ≤ c * Z q m h := by
        rw [← hcr]; linarith [k1]
      nlinarith [k1', k2, k3]

/-! ### The stationary inversion count -/
lemma exp_inv (θ : ℝ) (z : BinaryWord N) :
    Real.exp (-θ * binaryInversions z) = Real.exp (-θ) ^ inv z := by
  rw [binaryInversions_eq_inv, mul_comm, Real.exp_nat_mul]

lemma denom_eq (θ : ℝ) (h : ℕ) : ∑ y : BinaryWord N, zw θ h y = Z (Real.exp (-θ)) N h := by
  unfold Z zw
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hcount_eq_hc, exp_inv]

lemma numer_eq (θ : ℝ) (h : ℕ) :
    ∑ y : BinaryWord N, zw θ h y * binaryInversions y = W (Real.exp (-θ)) N h := by
  unfold W zw
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hcount_eq_hc, exp_inv, binaryInversions_eq_inv]
  split_ifs <;> simp

theorem zeta_inversions (θ : ℝ) (hθ : 0 < θ) (h : ℕ) (hh : h ≤ N) :
    ∑ z : BinaryWord N, zeta θ h z * binaryInversions z ≤ Real.pi ^ 2 / (6 * θ ^ 2) := by
  have hpos := denom_pos (N := N) θ h hh
  have e : ∑ z : BinaryWord N, zeta θ h z * binaryInversions z =
      W (Real.exp (-θ)) N h / Z (Real.exp (-θ)) N h := by
    unfold zeta
    rw [← numer_eq, ← denom_eq, Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [e]
  rw [denom_eq] at hpos
  have hq0 : 0 ≤ Real.exp (-θ) := (Real.exp_pos _).le
  have hq1 : Real.exp (-θ) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  rw [div_le_iff₀ hpos]
  exact (W_le _ hq0 hq1 N h).trans
    (mul_le_mul_of_nonneg_right (S_le θ hθ h) hpos.le)

end TranspositionIID.Main.Dev.L32.PartD
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
/-! ### Part E: the stationary inversion count -/
alias zeta_inversions := TranspositionIID.Main.Dev.L32.PartD.zeta_inversions

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
/-! ### Basic facts on `pre` -/
lemma pre_eq_sum (w : BinaryWord N) (j : ℕ) :
    pre w j = ∑ i : Fin N, if i.val < j ∧ w i = true then 1 else 0 := by
  unfold pre; rw [Finset.card_filter]

lemma pre_succ' (w : BinaryWord N) (j : ℕ) :
    pre w (j + 1) = pre w j + (if h : j < N then (if w ⟨j, h⟩ = true then 1 else 0) else 0) := by
  rw [pre_eq_sum, pre_eq_sum]
  have key : ∀ i : Fin N, (if i.val < j + 1 ∧ w i = true then 1 else 0) =
      (if i.val < j ∧ w i = true then 1 else 0) + (if i.val = j ∧ w i = true then 1 else 0) := by
    intro i
    by_cases h1 : i.val < j <;> by_cases h2 : i.val = j <;> by_cases h3 : w i = true <;>
      simp [h1, h2, h3] <;> omega
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib]
  congr 1
  by_cases h : j < N
  · rw [dif_pos h, Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      have : b.val ≠ j := fun e => hb (Fin.ext e)
      simp [this]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro i _
    have := i.isLt
    have : i.val ≠ j := by omega
    simp [this]

lemma pre_congr (u w : BinaryWord N) (j : ℕ) (h : ∀ i : Fin N, i.val < j → u i = w i) :
    pre u j = pre w j := by
  unfold pre
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (h i h1) ▸ h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (h i h1).symm ▸ h2⟩

lemma pre_min (w : BinaryWord N) (j : ℕ) : pre w j = pre w (min j N) := by
  unfold pre
  congr 1
  apply Finset.filter_congr
  intro i _
  have := i.isLt
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma hcount_eq_pre (w : BinaryWord N) : hcount w = pre w N := by
  unfold hcount pre
  congr 1
  apply Finset.filter_congr
  intro i _
  have := i.isLt
  constructor
  · intro h; exact ⟨this, h⟩
  · rintro ⟨_, h⟩; exact h

lemma pre_add_le (w : BinaryWord N) (j m : ℕ) : pre w (j + m) ≤ pre w j + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, pre_succ']
    split_ifs <;> omega

lemma pre_mono (w : BinaryWord N) (j m : ℕ) : pre w j ≤ pre w (j + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, pre_succ']
    omega

/-! ### Part F -/
theorem pre_le (w : BinaryWord N) (j : ℕ) : pre w j ≤ N := by
  unfold pre
  exact (Finset.card_filter_le _ _).trans (by simp)

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
alias pre_le := TranspositionIID.Main.Dev.L32.PartA.pre_le

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
theorem pre_N (w : BinaryWord N) : pre w N = hcount w := (hcount_eq_pre w).symm

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
alias pre_N := TranspositionIID.Main.Dev.L32.PartA.pre_N

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
theorem pre_zero (w : BinaryWord N) : pre w 0 = 0 := by
  simp [pre]

lemma pre_bot (h j : ℕ) : pre (bot N h) j = min j N - (N - h) := by
  induction j with
  | zero => simp [pre_zero]
  | succ j ih =>
    rw [pre_succ', ih]
    split_ifs with h1 h2
    · simp only [bot, decide_eq_true_eq] at h2; omega
    · simp only [bot, decide_eq_true_eq] at h2; omega
    · omega

theorem hcount_bot (h : ℕ) (hh : h ≤ N) : hcount (bot N h) = h := by
  rw [hcount_eq_pre, pre_bot]; omega

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
alias hcount_bot := TranspositionIID.Main.Dev.L32.PartA.hcount_bot

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
theorem bot_le (z : BinaryWord N) : wle (bot N (hcount z)) z := by
  intro j
  rw [pre_bot, pre_min z j]
  have h1 := pre_add_le z (min j N) (N - min j N)
  have h2 : min j N + (N - min j N) = N := by omega
  rw [h2, ← hcount_eq_pre] at h1
  omega

/-! ### Inversions as double sums -/
/-- indicator of an L letter -/
noncomputable def ell (w : BinaryWord N) (i : Fin N) : ℝ := if w i = false then 1 else 0

lemma inv_sum (w : BinaryWord N) : binaryInversions w =
    ∑ i : Fin N, ∑ j : Fin N, if i < j ∧ w i = false ∧ w j = true then (1 : ℝ) else 0 := by
  unfold binaryInversions
  rw [Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]

lemma pre_sum (w : BinaryWord N) : ∑ j ∈ Finset.range N, (pre w j : ℝ) =
    ∑ i : Fin N, ∑ j : Fin N, if i < j ∧ w i = true then (1 : ℝ) else 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => (pre w j : ℝ))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pre_eq_sum]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact if_congr Iff.rfl rfl rfl

noncomputable def dd (w : BinaryWord N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if i < j then ell w i * ell w j else 0

lemma partition (w : BinaryWord N) :
    binaryInversions w + ∑ j ∈ Finset.range N, (pre w j : ℝ) + dd w =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then (1 : ℝ) else 0 := by
  rw [inv_sum, pre_sum, dd, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i < j <;> cases hi : w i <;> cases hj : w j <;> simp [h, hi, hj, ell]

lemma ell_sum (w : BinaryWord N) : ∑ i, ell w i = (N : ℝ) - hcount w := by
  have : ∀ i, ell w i = 1 - (if w i = true then (1 : ℝ) else 0) := by
    intro i; cases hi : w i <;> simp [ell, hi]
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib]
  unfold hcount
  rw [Finset.card_filter]
  push_cast
  simp

lemma dd_eq (w : BinaryWord N) : 2 * dd w = (∑ i, ell w i) ^ 2 - ∑ i, ell w i := by
  have hsq : (∑ i, ell w i) ^ 2 = ∑ i : Fin N, ∑ j : Fin N, ell w i * ell w j := by
    rw [sq, Finset.sum_mul_sum]
  have hpt : ∀ i j : Fin N, ell w i * ell w j =
      (if i < j then ell w i * ell w j else 0) + (if j < i then ell w j * ell w i else 0) +
        (if i = j then ell w i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · have : ell w i * ell w i = ell w i := by unfold ell; split_ifs <;> simp
      simp [this]
    · simp [h, h.ne', not_lt.mpr h.le, mul_comm]
  have h2 : ∑ i : Fin N, ∑ j : Fin N, (if j < i then ell w j * ell w i else 0) = dd w := by
    rw [dd, Finset.sum_comm]
  rw [hsq, Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
  simp only [Finset.sum_add_distrib]
  rw [h2]
  simp [Finset.sum_ite_eq, dd]
  ring

theorem inversions_diff (w z : BinaryWord N) (h : hcount w = hcount z) :
    binaryInversions w - binaryInversions z =
      ∑ j ∈ Finset.range N, ((pre z j : ℝ) - pre w j) := by
  have hw := partition w
  have hz := partition z
  have hd : dd w = dd z := by
    have a := dd_eq w
    have b := dd_eq z
    rw [ell_sum] at a b
    rw [h] at a
    linarith
  rw [Finset.sum_sub_distrib]
  linarith

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
/-! ### Part F: inversion count in prefix counts; the bottom word -/
alias inversions_diff := TranspositionIID.Main.Dev.L32.PartA.inversions_diff

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
/-- indicator of an H letter -/
noncomputable def eta (w : BinaryWord N) (i : Fin N) : ℝ := if w i = true then 1 else 0

theorem inversions_le (w : BinaryWord N) : binaryInversions w ≤ (N : ℝ) ^ 2 / 4 := by
  have h1 : binaryInversions w ≤ (∑ i, ell w i) * ∑ j, eta w j := by
    rw [inv_sum, Finset.sum_mul_sum]
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    by_cases h : i < j <;> cases hi : w i <;> cases hj : w j <;> simp [h, hi, hj, ell, eta]
  have h2 : (∑ i, ell w i) + ∑ j, eta w j = N := by
    rw [← Finset.sum_add_distrib]
    have : ∀ i, ell w i + eta w i = 1 := by
      intro i; cases hi : w i <;> simp [ell, eta, hi]
    simp [this]
  nlinarith [sq_nonneg ((∑ i, ell w i) - ∑ j, eta w j)]

/-! ### Part A -/
lemma update_of_eq (w : BinaryWord N) (k : Fin (N - 1)) (b : Bool)
    (h : w ⟨k.val, by omega⟩ = w ⟨k.val + 1, by omega⟩) : exclusionUpdate w k b = w := by
  simp [exclusionUpdate, h]

lemma update_of_ne (w : BinaryWord N) (k : Fin (N - 1)) (b : Bool)
    (h : w ⟨k.val, by omega⟩ ≠ w ⟨k.val + 1, by omega⟩) (i : Fin N) :
    exclusionUpdate w k b i =
      if i.val = k.val then b else if i.val = k.val + 1 then !b else w i := by
  simp only [exclusionUpdate, h, if_false]
  simp [Fin.ext_iff]

theorem pre_update (w : BinaryWord N) (k : Fin (N - 1)) (b : Bool) (j : ℕ) :
    pre (exclusionUpdate w k b) j =
      if j = k.val + 1 then
        (if b then min (pre w k.val + 1) (pre w (k.val + 2))
         else max (pre w k.val) (pre w (k.val + 2) - 1))
      else pre w j := by
  have hk := k.isLt
  have p1 : pre w (k.val + 1) = pre w k.val +
      (if w ⟨k.val, by omega⟩ = true then 1 else 0) := by
    rw [pre_succ', dif_pos (by omega)]
  have p2 : pre w (k.val + 2) = pre w (k.val + 1) +
      (if w ⟨k.val + 1, by omega⟩ = true then 1 else 0) := by
    rw [pre_succ', dif_pos (by omega)]
  by_cases hac : w ⟨k.val, by omega⟩ = w ⟨k.val + 1, by omega⟩
  · rw [update_of_eq w k b hac]
    split_ifs with hj hb
    · subst hj
      rw [p2, p1]; rw [← hac]
      cases w ⟨k.val, by omega⟩ <;> simp
    · subst hj
      rw [p2, p1]; rw [← hac]
      cases w ⟨k.val, by omega⟩ <;> simp
    · rfl
  · have hu := update_of_ne w k b hac
    set u := exclusionUpdate w k b with hu_def
    have hlow : pre u k.val = pre w k.val := by
      apply pre_congr; intro i hi
      rw [hu]; simp [show i.val ≠ k.val by omega, show i.val ≠ k.val + 1 by omega]
    have hlow' : ∀ j, j ≤ k.val → pre u j = pre w j := by
      intro j hj; apply pre_congr; intro i hi
      rw [hu]; simp [show i.val ≠ k.val by omega, show i.val ≠ k.val + 1 by omega]
    have q1 : pre u (k.val + 1) = pre w k.val + (if b then 1 else 0) := by
      rw [pre_succ', dif_pos (by omega), hlow, hu]
      simp
    have q2 : pre u (k.val + 2) = pre u (k.val + 1) + (if !b then 1 else 0) := by
      rw [pre_succ', dif_pos (by omega), hu]
      simp
    have q2' : pre u (k.val + 2) = pre w (k.val + 2) := by
      rw [q2, q1, p2, p1]
      revert hac
      cases w ⟨k.val, by omega⟩ <;> cases w ⟨k.val + 1, by omega⟩ <;> cases b <;> simp
    have hhigh : ∀ m, pre u (k.val + 2 + m) = pre w (k.val + 2 + m) := by
      intro m
      induction m with
      | zero => simpa using q2'
      | succ m ih =>
        rw [← add_assoc, pre_succ', pre_succ', ih]
        congr 1
        by_cases hm : k.val + 2 + m < N
        · rw [dif_pos hm, dif_pos hm, hu]
          simp [show k.val + 2 + m ≠ k.val by omega, show k.val + 2 + m ≠ k.val + 1 by omega]
        · rw [dif_neg hm, dif_neg hm]
    split_ifs with hj hb
    · subst hj; subst hb
      rw [q1, p2, p1]
      revert hac
      cases w ⟨k.val, by omega⟩ <;> cases w ⟨k.val + 1, by omega⟩ <;> simp
    · subst hj
      rw [q1, p2, p1]
      simp only [Bool.not_eq_true] at hb
      subst hb
      revert hac
      cases w ⟨k.val, by omega⟩ <;> cases w ⟨k.val + 1, by omega⟩ <;> simp
    · by_cases hjk : j ≤ k.val
      · exact hlow' j hjk
      · obtain ⟨m, rfl⟩ : ∃ m, j = k.val + 2 + m := ⟨j - (k.val + 2), by omega⟩
        exact hhigh m

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
theorem update_mono (w z : BinaryWord N) (k : Fin (N - 1)) (b : Bool) (h : wle w z) :
    wle (exclusionUpdate w k b) (exclusionUpdate z k b) := by
  intro j
  rw [pre_update, pre_update]
  have h0 := h k.val
  have h2 := h (k.val + 2)
  split_ifs
  · omega
  · omega
  · exact h j

lemma qH_pos (θ : ℝ) : 0 < qH θ := by
  unfold qH; positivity

lemma qH_le_one (θ : ℝ) : qH θ ≤ 1 := by
  unfold qH
  rw [div_le_one (by positivity)]
  linarith [Real.exp_pos (-θ)]

theorem kernel_apply (θ : ℝ) (w : BinaryWord N) (f : BinaryWord N → ℝ) :
    ∑ z, exclusionKernel N θ w z * f z =
      ∑ k : Fin (N - 1), (qH θ * f (exclusionUpdate w k true) +
        (1 - qH θ) * f (exclusionUpdate w k false)) / ((N - 1 : ℕ) : ℝ) := by
  unfold exclusionKernel
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hpt : ∀ z, ((if exclusionUpdate w k true = z then 1 / (1 + Real.exp (-θ)) else 0) +
      (if exclusionUpdate w k false = z then 1 - 1 / (1 + Real.exp (-θ)) else 0)) /
        ((N - 1 : ℕ) : ℝ) * f z =
      (if exclusionUpdate w k true = z then
          qH θ * f (exclusionUpdate w k true) / ((N - 1 : ℕ) : ℝ) else 0) +
      (if exclusionUpdate w k false = z then
          (1 - qH θ) * f (exclusionUpdate w k false) / ((N - 1 : ℕ) : ℝ) else 0) := by
    intro z
    unfold qH
    by_cases h1 : exclusionUpdate w k true = z <;> by_cases h2 : exclusionUpdate w k false = z <;>
      simp only [h1, h2, if_true, if_false] <;> ring
  rw [Finset.sum_congr rfl (fun z _ => hpt z), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
/-! ### Part A: kernel basics, monotonicity, linear identity -/

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
theorem kernel_nonneg (θ : ℝ) (w z : BinaryWord N) : 0 ≤ exclusionKernel N θ w z := by
  unfold exclusionKernel
  have h1 := qH_pos θ
  have h2 := qH_le_one θ
  unfold qH at h1 h2
  apply Finset.sum_nonneg
  intro k _
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply add_nonneg
  · split_ifs <;> linarith
  · split_ifs <;> linarith

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
theorem kernel_pow_nonneg (θ : ℝ) (t : ℕ) (w z : BinaryWord N) :
    0 ≤ (exclusionKernel N θ ^ t) w z := by
  induction t generalizing z with
  | zero =>
    rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (ih y) (kernel_nonneg θ y z))

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
alias kernel_pow_nonneg := TranspositionIID.Main.Dev.L32.PartA.kernel_pow_nonneg

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
lemma kernel_row (hN : 2 ≤ N) (θ : ℝ) (w : BinaryWord N) :
    ∑ z, exclusionKernel N θ w z = 1 := by
  have := kernel_apply θ w (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  have hN1 : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 1 ≤ N - 1 := by omega
    exact_mod_cast (by omega : N - 1 ≠ 0)
  simp only [add_sub_cancel, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem kernel_pow_row (hN : 2 ≤ N) (θ : ℝ) (t : ℕ) (w : BinaryWord N) :
    ∑ z, (exclusionKernel N θ ^ t) w z = 1 := by
  induction t with
  | zero =>
    simp [Matrix.one_apply]
  | succ t ih =>
    rw [pow_succ]
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, kernel_row hN, mul_one]
    exact ih

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
alias kernel_pow_row := TranspositionIID.Main.Dev.L32.PartA.kernel_pow_row

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
lemma kernel_ne_zero (θ : ℝ) (w z : BinaryWord N) (h : exclusionKernel N θ w z ≠ 0) :
    ∃ k b, exclusionUpdate w k b = z := by
  by_contra hc
  push Not at hc
  apply h
  unfold exclusionKernel
  apply Finset.sum_eq_zero
  intro k _
  simp [hc k true, hc k false]

lemma hcount_update (w : BinaryWord N) (k : Fin (N - 1)) (b : Bool) :
    hcount (exclusionUpdate w k b) = hcount w := by
  have := k.isLt
  rw [hcount_eq_pre, hcount_eq_pre, pre_update, if_neg (by omega)]

theorem kernel_pow_class (θ : ℝ) (t : ℕ) (w z : BinaryWord N)
    (h : (exclusionKernel N θ ^ t) w z ≠ 0) : hcount z = hcount w := by
  induction t generalizing z with
  | zero =>
    rw [pow_zero, Matrix.one_apply] at h
    split_ifs at h with hwz
    · rw [hwz]
    · exact absurd rfl h
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hy1 : (exclusionKernel N θ ^ t) w y ≠ 0 := left_ne_zero_of_mul hy
    have hy2 : exclusionKernel N θ y z ≠ 0 := right_ne_zero_of_mul hy
    obtain ⟨k, b, rfl⟩ := kernel_ne_zero θ y _ hy2
    rw [hcount_update]
    exact ih y hy1

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
alias kernel_pow_class := TranspositionIID.Main.Dev.L32.PartA.kernel_pow_class

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
lemma expectedAfter_succ (P : Matrix (BinaryWord N) (BinaryWord N) ℝ) (w : BinaryWord N)
    (t : ℕ) (f : BinaryWord N → ℝ) :
    expectedAfter P w (t + 1) f = ∑ y, P w y * expectedAfter P y t f := by
  unfold expectedAfter
  rw [pow_succ']
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem expectedAfter_mono (θ : ℝ) (t : ℕ) (f : BinaryWord N → ℝ) (hf : MonoW f) :
    MonoW (fun w => expectedAfter (exclusionKernel N θ) w t f) := by
  induction t with
  | zero =>
    intro w z h
    simp only [expectedAfter, pow_zero, Matrix.one_apply]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hf w z h
  | succ t ih =>
    intro w z h
    simp only [expectedAfter_succ]
    rw [kernel_apply θ w (fun y => expectedAfter (exclusionKernel N θ) y t f),
      kernel_apply θ z (fun y => expectedAfter (exclusionKernel N θ) y t f)]
    apply Finset.sum_le_sum
    intro k _
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have h1 := qH_pos θ
    have h2 := qH_le_one θ
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (ih _ _ (update_mono w z k true h)) h1.le
    · exact mul_le_mul_of_nonneg_left (ih _ _ (update_mono w z k false h)) (by linarith)

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
alias expectedAfter_mono := TranspositionIID.Main.Dev.L32.PartA.expectedAfter_mono

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
lemma rho_local (ρ : ℝ) (hρ : 0 < ρ) (a c : ℕ) (hac : a ≤ c) (hca : c ≤ a + 2) :
    1 / (1 + ρ) * ρ ^ (min (a + 1) c) + (1 - 1 / (1 + ρ)) * ρ ^ (max a (c - 1)) =
      ρ / (1 + ρ) * ρ ^ a + 1 / (1 + ρ) * ρ ^ c := by
  have h1 : (1 + ρ) ≠ 0 := by positivity
  obtain ⟨d, rfl⟩ : ∃ d, c = a + d := ⟨c - a, by omega⟩
  have hd : d ≤ 2 := by omega
  interval_cases d
  · rw [show min (a + 1) (a + 0) = a by omega, show max a (a + 0 - 1) = a by omega]
    field_simp; ring
  · rw [show min (a + 1) (a + 1) = a + 1 by omega, show max a (a + 1 - 1) = a by omega]
    field_simp; ring
  · rw [show min (a + 1) (a + 2) = a + 1 by omega, show max a (a + 2 - 1) = a + 1 by omega]
    field_simp; ring

theorem kernel_rho (hN : 2 ≤ N) (θ : ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N - 1)
    (w : BinaryWord N) :
    ∑ z, exclusionKernel N θ w z * Real.exp (-θ) ^ pre z j =
      (1 - 1 / ((N - 1 : ℕ) : ℝ)) * Real.exp (-θ) ^ pre w j +
        (1 / ((N - 1 : ℕ) : ℝ)) *
          (Real.exp (-θ) / (1 + Real.exp (-θ)) * Real.exp (-θ) ^ pre w (j - 1) +
            1 / (1 + Real.exp (-θ)) * Real.exp (-θ) ^ pre w (j + 1)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [kernel_apply θ w (fun z => Real.exp (-θ) ^ pre z (i + 1))]
  simp only [Nat.add_sub_cancel]
  have hρ0 : 0 < Real.exp (-θ) := Real.exp_pos _
  have hq : qH θ = 1 / (1 + Real.exp (-θ)) := rfl
  have hN1 : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N - 1 ≠ 0)
  have hpa : pre w i ≤ pre w (i + 1 + 1) := by
    have := pre_mono w i 2; simpa [add_assoc] using this
  have hpb : pre w (i + 1 + 1) ≤ pre w i + 2 := by
    have := pre_add_le w i 2; simpa [add_assoc] using this
  set ρ := Real.exp (-θ) with hρ
  set p := ρ ^ pre w (i + 1) with hp
  set C := ρ / (1 + ρ) * ρ ^ pre w i + 1 / (1 + ρ) * ρ ^ pre w (i + 1 + 1) with hC
  have hterm : ∀ k : Fin (N - 1),
      (qH θ * ρ ^ pre (exclusionUpdate w k true) (i + 1) +
        (1 - qH θ) * ρ ^ pre (exclusionUpdate w k false) (i + 1)) / ((N - 1 : ℕ) : ℝ) =
      (p + if k.val = i then C - p else 0) / ((N - 1 : ℕ) : ℝ) := by
    intro k
    congr 1
    rw [pre_update, pre_update]
    by_cases hk : k.val = i
    · subst hk
      simp only [if_true, Bool.false_eq_true, if_false]
      rw [hq, rho_local ρ hρ0 _ _ hpa hpb]
      ring
    · have : ¬ (i + 1 = k.val + 1) := by omega
      simp only [this, if_false, hk]
      ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_div, Finset.sum_add_distrib]
  have hs : ∑ k : Fin (N - 1), (if k.val = i then C - p else 0) = C - p := by
    rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin (N - 1))]
    · simp
    · intro b _ hb
      have : b.val ≠ i := fun e => hb (Fin.ext e)
      simp [this]
    · simp
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
alias kernel_rho := TranspositionIID.Main.Dev.L32.PartA.kernel_rho

alias inversions_le := TranspositionIID.Main.Dev.L32.PartA.inversions_le

alias bot_le := TranspositionIID.Main.Dev.L32.PartA.bot_le

alias pre_zero := TranspositionIID.Main.Dev.L32.PartA.pre_zero

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartG
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
/-! ### Dominance -/
lemma sum_ind_eq (x M : ℕ) :
    ∑ m ∈ Finset.range M, (if m + 1 ≤ x then (1 : ℝ) else 0) = ((min x M : ℕ) : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hx : M + 1 ≤ x
    · rw [if_pos hx, min_eq_right (by omega : M ≤ x), min_eq_right hx]; push_cast; ring
    · rw [if_neg hx, add_zero, show min x M = min x (M + 1) by omega]

lemma sum_geom_ind_eq (ρ : ℝ) (x M : ℕ) :
    ∑ m ∈ Finset.range M, ρ ^ m * (1 - ρ) * (if m + 1 ≤ x then (1 : ℝ) else 0) =
      1 - ρ ^ (min x M) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hx : M + 1 ≤ x
    · rw [if_pos hx, min_eq_right (by omega : M ≤ x), min_eq_right hx, pow_succ]; ring
    · rw [if_neg hx, mul_zero, add_zero, show min x M = min x (M + 1) by omega]

theorem dominance {S : Type*} [Fintype S] (ν₁ ν₂ : S → ℝ) (h₁ : ∀ s, 0 ≤ ν₁ s)
    (h₂ : ∀ s, 0 ≤ ν₂ s) (hsum : ∑ s, ν₁ s = ∑ s, ν₂ s) (X : S → ℕ) (M : ℕ) (hM : 1 ≤ M)
    (hX : ∀ s, X s ≤ M) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hdom : ∀ m : ℕ, ∑ s, ν₁ s * (if m ≤ X s then 1 else 0) ≤
      ∑ s, ν₂ s * (if m ≤ X s then 1 else 0)) :
    ∑ s, ν₂ s * (X s : ℝ) - ∑ s, ν₁ s * (X s : ℝ) ≤
      (∑ s, ν₁ s * ρ ^ X s - ∑ s, ν₂ s * ρ ^ X s) / (ρ ^ (M - 1) * (1 - ρ)) := by
  have hX' : ∀ s, (X s : ℝ) =
      ∑ m ∈ Finset.range M, (if m + 1 ≤ X s then (1 : ℝ) else 0) := by
    intro s; rw [sum_ind_eq, min_eq_left (hX s)]
  have hρ' : ∀ s, ρ ^ X s =
      1 - ∑ m ∈ Finset.range M, ρ ^ m * (1 - ρ) * (if m + 1 ≤ X s then (1 : ℝ) else 0) := by
    intro s; rw [sum_geom_ind_eq, min_eq_left (hX s)]; ring
  have keyX : ∀ ν : S → ℝ, ∑ s, ν s * (X s : ℝ) =
      ∑ m ∈ Finset.range M, ∑ s, ν s * (if m + 1 ≤ X s then (1 : ℝ) else 0) := by
    intro ν
    simp only [hX', Finset.mul_sum]
    exact Finset.sum_comm
  have keyρ : ∀ ν : S → ℝ, ∑ s, ν s * ρ ^ X s = ∑ s, ν s -
      ∑ m ∈ Finset.range M, ρ ^ m * (1 - ρ) *
        ∑ s, ν s * (if m + 1 ≤ X s then (1 : ℝ) else 0) := by
    intro ν
    simp only [hρ', mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro s _
    ring
  rw [keyX, keyX, keyρ, keyρ, hsum, ← Finset.sum_sub_distrib, sub_sub_sub_cancel_left,
    ← Finset.sum_sub_distrib]
  have hK : 0 < ρ ^ (M - 1) * (1 - ρ) := mul_pos (pow_pos hρ0 _) (by linarith)
  rw [le_div_iff₀ hK, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mem_range] at hm
  have hD := hdom (m + 1)
  have hpow : ρ ^ (M - 1) ≤ ρ ^ m := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
  rw [← mul_sub]
  have hD' : 0 ≤ ∑ s, ν₂ s * (if m + 1 ≤ X s then (1 : ℝ) else 0) -
      ∑ s, ν₁ s * (if m + 1 ≤ X s then (1 : ℝ) else 0) := by linarith
  have h1ρ : 0 ≤ 1 - ρ := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hpow h1ρ]

end TranspositionIID.Main.Dev.L32.PartG
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
/-! ### Part G: comparison of expectations under stochastic domination -/

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartG
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
/-! ### Contraction -/
/-- The weights `exp(θ j/2) j (N-j)`. -/
noncomputable def phi (N : ℕ) (θ : ℝ) (j : ℕ) : ℝ :=
  Real.exp (θ * j / 2) * j * ((N : ℝ) - j)

lemma phi_zero (N : ℕ) (θ : ℝ) : phi N θ 0 = 0 := by simp [phi]

lemma phi_N (N : ℕ) (θ : ℝ) : phi N θ N = 0 := by simp [phi]

lemma phi_nonneg (N : ℕ) (θ : ℝ) (j : ℕ) (hj : j ≤ N) : 0 ≤ phi N θ j := by
  unfold phi
  have : (j : ℝ) ≤ N := by exact_mod_cast hj
  have h2 : 0 ≤ (N : ℝ) - j := by linarith
  positivity

lemma phi_ge_one (N : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (j : ℕ) (hj1 : 1 ≤ j) (hjN : j + 1 ≤ N) :
    1 ≤ phi N θ j := by
  unfold phi
  have hx : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hxN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
  have he : 1 ≤ Real.exp (θ * j / 2) := Real.one_le_exp (by positivity)
  have hψ : 1 ≤ (j : ℝ) * ((N : ℝ) - j) := by nlinarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ Real.exp (θ * j / 2) * ((j : ℝ) * ((N : ℝ) - j)) :=
        mul_le_mul he hψ zero_le_one (by linarith)
    _ = _ := by ring

lemma phi_le (N : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (j : ℕ) (hj : j ≤ N) :
    phi N θ j ≤ Real.exp (θ * N / 2) * (N : ℝ) ^ 2 := by
  unfold phi
  have hx : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hx0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have he : Real.exp (θ * j / 2) ≤ Real.exp (θ * N / 2) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hψ : (j : ℝ) * ((N : ℝ) - j) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hψ0 : 0 ≤ (j : ℝ) * ((N : ℝ) - j) := mul_nonneg hx0 (by linarith)
  calc Real.exp (θ * j / 2) * j * ((N : ℝ) - j)
      = Real.exp (θ * j / 2) * ((j : ℝ) * ((N : ℝ) - j)) := by ring
    _ ≤ Real.exp (θ * N / 2) * (N : ℝ) ^ 2 :=
        mul_le_mul he hψ hψ0 (Real.exp_pos _).le

lemma phi_key (N : ℕ) (θ : ℝ) (hθ : 0 < θ) (j : ℕ) (hj1 : 1 ≤ j) (hjN : j + 1 ≤ N) :
    Real.exp (-θ) / (1 + Real.exp (-θ)) * phi N θ (j + 1) +
      1 / (1 + Real.exp (-θ)) * phi N θ (j - 1) ≤ (1 - 4 / (N : ℝ) ^ 2) * phi N θ j := by
  set r := Real.exp (θ / 2) with hr
  set E := Real.exp (θ * j / 2) with hE
  have hr0 : 0 < r := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  have hx : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hxN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
  have h1 : phi N θ (j + 1) = E * r * (((j : ℝ) + 1) * ((N : ℝ) - j - 1)) := by
    unfold phi; push_cast
    rw [show θ * ((j : ℝ) + 1) / 2 = θ * j / 2 + θ / 2 by ring, Real.exp_add]; ring
  have h2 : phi N θ (j - 1) = E * r⁻¹ * (((j : ℝ) - 1) * ((N : ℝ) - j + 1)) := by
    unfold phi; rw [Nat.cast_sub hj1]; push_cast
    rw [show θ * ((j : ℝ) - 1) / 2 = θ * j / 2 + -(θ / 2) by ring, Real.exp_add, Real.exp_neg]
    ring
  have h0 : phi N θ j = E * ((j : ℝ) * ((N : ℝ) - j)) := by unfold phi; ring
  have hrr : r * r = Real.exp θ := by rw [hr, ← Real.exp_add]; ring_nf
  have hρ : Real.exp (-θ) = (r * r)⁻¹ := by rw [hrr, Real.exp_neg]
  have hs1 : Real.exp (-θ) / (1 + Real.exp (-θ)) * r = r / (r ^ 2 + 1) := by
    rw [hρ]; field_simp
  have hs2 : 1 / (1 + Real.exp (-θ)) * r⁻¹ = r / (r ^ 2 + 1) := by
    rw [hρ]; field_simp
  have hs : r / (r ^ 2 + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (r - 1)]
  have hs0 : 0 ≤ r / (r ^ 2 + 1) := by positivity
  rw [h1, h2, h0]
  set ψ := (j : ℝ) * ((N : ℝ) - j) with hψ
  have hψ1 : 1 ≤ ψ := by rw [hψ]; nlinarith
  have hψN : 4 / (N : ℝ) ^ 2 * ψ ≤ 1 := by
    have hN0 : 0 < (N : ℝ) := by linarith
    rw [div_mul_eq_mul_div, div_le_one (by positivity), hψ]
    nlinarith [sq_nonneg ((N : ℝ) - 2 * j)]
  calc Real.exp (-θ) / (1 + Real.exp (-θ)) * (E * r * (((j : ℝ) + 1) * ((N : ℝ) - j - 1))) +
        1 / (1 + Real.exp (-θ)) * (E * r⁻¹ * (((j : ℝ) - 1) * ((N : ℝ) - j + 1)))
      = E * (Real.exp (-θ) / (1 + Real.exp (-θ)) * r) * (((j : ℝ) + 1) * ((N : ℝ) - j - 1)) +
        E * (1 / (1 + Real.exp (-θ)) * r⁻¹) * (((j : ℝ) - 1) * ((N : ℝ) - j + 1)) := by ring
    _ = E * (r / (r ^ 2 + 1)) * (2 * ψ - 2) := by rw [hs1, hs2, hψ]; ring
    _ ≤ E * (1 / 2) * (2 * ψ - 2) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hs hE0.le
    _ = E * (ψ - 1) := by ring
    _ ≤ (1 - 4 / (N : ℝ) ^ 2) * (E * ψ) := by
        nlinarith [mul_nonneg hE0.le (sub_nonneg.2 hψN)]

theorem contraction (N : ℕ) (hN : 2 ≤ N) (θ : ℝ) (hθ : 0 < θ) (e : ℕ → ℕ → ℝ)
    (he0 : ∀ t, e t 0 = 0) (heN : ∀ t, e t N = 0) (hnn : ∀ t j, 0 ≤ e t j)
    (hinit : ∀ j, e 0 j ≤ 1)
    (hrec : ∀ t j, 1 ≤ j → j ≤ N - 1 →
      e (t + 1) j ≤ (1 - 1 / ((N - 1 : ℕ) : ℝ)) * e t j +
        (1 / ((N - 1 : ℕ) : ℝ)) *
          (Real.exp (-θ) / (1 + Real.exp (-θ)) * e t (j - 1) +
            1 / (1 + Real.exp (-θ)) * e t (j + 1)))
    (t : ℕ) :
    ∑ j ∈ Finset.range N, e t j ≤
      (N : ℝ) ^ 3 * Real.exp (θ * N / 2) * Real.exp (-(4 * t : ℝ) / (N : ℝ) ^ 3) := by
  set c : ℝ := 1 / ((N - 1 : ℕ) : ℝ) with hc
  set α : ℝ := Real.exp (-θ) / (1 + Real.exp (-θ)) with hα
  set β : ℝ := 1 / (1 + Real.exp (-θ)) with hβ
  set Φ : ℕ → ℝ := fun t => ∑ j ∈ Finset.range N, phi N θ j * e t j with hΦ
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N - 1)
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one (by linarith)]; exact hN1
  have hcN : 1 / (N : ℝ) ≤ c := by
    rw [hc]; apply one_div_le_one_div_of_le (by linarith)
    exact_mod_cast (by omega : N - 1 ≤ N)
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have shift1 : ∀ t, ∑ j ∈ Finset.range N, phi N θ j * e t (j - 1) =
      ∑ j ∈ Finset.range N, phi N θ (j + 1) * e t j := by
    intro t
    have a := Finset.sum_range_succ (fun j => phi N θ j * e t (j - 1)) N
    have b := Finset.sum_range_succ' (fun j => phi N θ j * e t (j - 1)) N
    simp only [phi_N, phi_zero, zero_mul, add_zero, Nat.add_sub_cancel] at a b
    rw [← a, b]
  have shift2 : ∀ t, ∑ j ∈ Finset.range N, phi N θ j * e t (j + 1) =
      ∑ j ∈ Finset.range N, phi N θ (j - 1) * e t j := by
    intro t
    have a := Finset.sum_range_succ (fun j => phi N θ (j - 1) * e t j) N
    have b := Finset.sum_range_succ' (fun j => phi N θ (j - 1) * e t j) N
    simp only [heN, he0, mul_zero, add_zero, Nat.add_sub_cancel] at a b
    rw [← a, b]
  have Φnn : ∀ t, 0 ≤ Φ t := fun t => Finset.sum_nonneg (fun j hj =>
    mul_nonneg (phi_nonneg N θ j (by rw [Finset.mem_range] at hj; omega)) (hnn t j))
  have step : ∀ t, Φ (t + 1) ≤ (1 - 4 / (N : ℝ) ^ 3) * Φ t := by
    intro t
    have h1 : Φ (t + 1) ≤ ∑ j ∈ Finset.range N,
        phi N θ j * ((1 - c) * e t j + c * (α * e t (j - 1) + β * e t (j + 1))) := by
      apply Finset.sum_le_sum; intro j hj; rw [Finset.mem_range] at hj
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · simp [phi_zero]
      · exact mul_le_mul_of_nonneg_left (hrec t j hj1 (by omega)) (phi_nonneg N θ j hj.le)
    have h2 : ∑ j ∈ Finset.range N,
        phi N θ j * ((1 - c) * e t j + c * (α * e t (j - 1) + β * e t (j + 1))) =
        (1 - c) * Φ t + c * ∑ j ∈ Finset.range N,
          e t j * (α * phi N θ (j + 1) + β * phi N θ (j - 1)) := by
      have e1 : ∑ j ∈ Finset.range N,
          phi N θ j * ((1 - c) * e t j + c * (α * e t (j - 1) + β * e t (j + 1))) =
          ∑ j ∈ Finset.range N, ((1 - c) * (phi N θ j * e t j) +
            (c * α) * (phi N θ j * e t (j - 1)) + (c * β) * (phi N θ j * e t (j + 1))) :=
        Finset.sum_congr rfl (fun j _ => by ring)
      have e2 : ∑ j ∈ Finset.range N, e t j * (α * phi N θ (j + 1) + β * phi N θ (j - 1)) =
          ∑ j ∈ Finset.range N, (α * (phi N θ (j + 1) * e t j) +
            β * (phi N θ (j - 1) * e t j)) :=
        Finset.sum_congr rfl (fun j _ => by ring)
      rw [e1, e2, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, shift1, shift2]
      ring
    have h3 : ∑ j ∈ Finset.range N, e t j * (α * phi N θ (j + 1) + β * phi N θ (j - 1)) ≤
        (1 - 4 / (N : ℝ) ^ 2) * Φ t := by
      rw [hΦ, Finset.mul_sum]
      apply Finset.sum_le_sum; intro j hj; rw [Finset.mem_range] at hj
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · simp [he0, phi_zero]
      · calc e t j * (α * phi N θ (j + 1) + β * phi N θ (j - 1))
            ≤ e t j * ((1 - 4 / (N : ℝ) ^ 2) * phi N θ j) :=
              mul_le_mul_of_nonneg_left (phi_key N θ hθ j hj1 (by omega)) (hnn t j)
          _ = _ := by ring
    have h4 : 4 / (N : ℝ) ^ 3 ≤ 4 * c / (N : ℝ) ^ 2 := by
      rw [show (4 : ℝ) / (N : ℝ) ^ 3 = 4 * (1 / (N : ℝ)) / (N : ℝ) ^ 2 by field_simp]
      gcongr
    have h5 : (1 - c) * Φ t + c * ((1 - 4 / (N : ℝ) ^ 2) * Φ t) =
        (1 - 4 * c / (N : ℝ) ^ 2) * Φ t := by ring
    have h6 := Φnn t
    calc Φ (t + 1) ≤ (1 - c) * Φ t + c * ((1 - 4 / (N : ℝ) ^ 2) * Φ t) := by
          have h7 := mul_le_mul_of_nonneg_left h3 hc0
          rw [h2] at h1; linarith
      _ = (1 - 4 * c / (N : ℝ) ^ 2) * Φ t := h5
      _ ≤ (1 - 4 / (N : ℝ) ^ 3) * Φ t := mul_le_mul_of_nonneg_right (by linarith) h6
  have hq0 : 0 ≤ 1 - 4 / (N : ℝ) ^ 3 := by
    have : (2 : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hN2 3
    have : (8 : ℝ) ≤ (N : ℝ) ^ 3 := by norm_num at this; linarith
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have iter : ∀ t, Φ t ≤ (1 - 4 / (N : ℝ) ^ 3) ^ t * Φ 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      calc Φ (t + 1) ≤ (1 - 4 / (N : ℝ) ^ 3) * Φ t := step t
        _ ≤ (1 - 4 / (N : ℝ) ^ 3) * ((1 - 4 / (N : ℝ) ^ 3) ^ t * Φ 0) :=
            mul_le_mul_of_nonneg_left ih hq0
        _ = _ := by ring
  have hq : 1 - 4 / (N : ℝ) ^ 3 ≤ Real.exp (-(4 / (N : ℝ) ^ 3)) := by
    linarith [Real.add_one_le_exp (-(4 / (N : ℝ) ^ 3))]
  have hqt : (1 - 4 / (N : ℝ) ^ 3) ^ t ≤ Real.exp (-(4 * t : ℝ) / (N : ℝ) ^ 3) := by
    calc (1 - 4 / (N : ℝ) ^ 3) ^ t ≤ Real.exp (-(4 / (N : ℝ) ^ 3)) ^ t :=
          pow_le_pow_left₀ hq0 hq t
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hΦ0 : Φ 0 ≤ (N : ℝ) ^ 3 * Real.exp (θ * N / 2) := by
    calc Φ 0 ≤ ∑ j ∈ Finset.range N, Real.exp (θ * N / 2) * (N : ℝ) ^ 2 := by
          apply Finset.sum_le_sum; intro j hj; rw [Finset.mem_range] at hj
          calc phi N θ j * e 0 j ≤ phi N θ j * 1 :=
                mul_le_mul_of_nonneg_left (hinit j) (phi_nonneg N θ j hj.le)
            _ ≤ _ := by rw [mul_one]; exact phi_le N θ hθ.le j hj.le
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hlow : ∑ j ∈ Finset.range N, e t j ≤ Φ t := by
    apply Finset.sum_le_sum; intro j hj; rw [Finset.mem_range] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · simp [he0]
    · exact le_mul_of_one_le_left (hnn t j) (phi_ge_one N θ hθ.le j hj1 (by omega))
  calc ∑ j ∈ Finset.range N, e t j ≤ Φ t := hlow
    _ ≤ (1 - 4 / (N : ℝ) ^ 3) ^ t * Φ 0 := iter t
    _ ≤ Real.exp (-(4 * t : ℝ) / (N : ℝ) ^ 3) * ((N : ℝ) ^ 3 * Real.exp (θ * N / 2)) :=
        mul_le_mul hqt hΦ0 (Φnn 0) (Real.exp_pos _).le
    _ = _ := by ring

end TranspositionIID.Main.Dev.L32.PartG
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
/-! ### Part H: contraction of the linear recursion -/

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartG
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
variable {N : ℕ}
/-! ### Assembly of Lemma 3.2 -/
lemma hcount_le (w : BinaryWord N) : hcount w ≤ N := by
  rw [← pre_N]; exact pre_le w N

lemma sum_class_const (μ : BinaryWord N → ℝ) (h : ℕ) (hμ : ∑ z, μ z = 1)
    (hcl : ∀ z, μ z ≠ 0 → hcount z = h) (f : BinaryWord N → ℝ) (c : ℝ)
    (hf : ∀ z, hcount z = h → f z = c) : ∑ z, μ z * f z = c := by
  calc ∑ z, μ z * f z = ∑ z, μ z * c := by
        apply Finset.sum_congr rfl; intro z _
        by_cases hz : μ z = 0
        · simp [hz]
        · rw [hf z (hcl z hz)]
    _ = c := by rw [← Finset.sum_mul, hμ, one_mul]

lemma inv_affine (μ : BinaryWord N → ℝ) (h : ℕ) (hh : h ≤ N) (hμ : ∑ z, μ z = 1)
    (hcl : ∀ z, μ z ≠ 0 → hcount z = h) :
    ∑ z, μ z * binaryInversions z = binaryInversions (bot N h) +
      ∑ j ∈ Finset.range N, ((pre (bot N h) j : ℝ) - ∑ z, μ z * (pre z j : ℝ)) := by
  have key : ∀ z, μ z * binaryInversions z = μ z * binaryInversions (bot N h) +
      ∑ j ∈ Finset.range N, μ z * ((pre (bot N h) j : ℝ) - pre z j) := by
    intro z
    rw [← Finset.mul_sum, ← mul_add]
    by_cases hz : μ z = 0
    · simp [hz]
    · congr 1
      have := inversions_diff z (bot N h) (by rw [hcl z hz, hcount_bot h hh])
      linarith
  rw [Finset.sum_congr rfl (fun z _ => key z), Finset.sum_add_distrib, ← Finset.sum_mul, hμ,
    one_mul, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl; intro j _
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ, one_mul]

lemma stat_lower (hN : 2 ≤ N) (θ : ℝ) (h : ℕ) (hh : h ≤ N) (t : ℕ)
    (f : BinaryWord N → ℝ) (hf : MonoW f) :
    expectedAfter (exclusionKernel N θ) (bot N h) t f ≤ ∑ a, zeta θ h a * f a := by
  rw [← zeta_stationary hN θ h hh t f]
  calc expectedAfter (exclusionKernel N θ) (bot N h) t f =
        ∑ a, zeta θ h a * expectedAfter (exclusionKernel N θ) (bot N h) t f := by
        rw [← Finset.sum_mul, zeta_sum θ h hh, one_mul]
    _ ≤ _ := by
        apply Finset.sum_le_sum; intro a _
        by_cases hz : zeta θ h a = 0
        · simp [hz]
        · apply mul_le_mul_of_nonneg_left _ (zeta_nonneg θ h a)
          have := bot_le a
          rw [zeta_class θ h a hz] at this
          exact expectedAfter_mono θ t f hf _ _ this

lemma rho_avg (hN : 2 ≤ N) (θ : ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N - 1)
    (μ : BinaryWord N → ℝ) :
    ∑ y, μ y * ∑ z, exclusionKernel N θ y z * Real.exp (-θ) ^ pre z j =
      (1 - 1 / ((N - 1 : ℕ) : ℝ)) * ∑ y, μ y * Real.exp (-θ) ^ pre y j +
        (1 / ((N - 1 : ℕ) : ℝ)) *
          (Real.exp (-θ) / (1 + Real.exp (-θ)) * ∑ y, μ y * Real.exp (-θ) ^ pre y (j - 1) +
            1 / (1 + Real.exp (-θ)) * ∑ y, μ y * Real.exp (-θ) ^ pre y (j + 1)) := by
  simp only [kernel_rho hN θ j hj1 hjN, Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro y _; ring

lemma gap_bound (hN : 2 ≤ N) (θ : ℝ) (hθ : 0 < θ) (w : BinaryWord N) (t : ℕ) :
    expectedAfter (exclusionKernel N θ) w t binaryInversions ≤
      ∑ z : BinaryWord N, zeta θ (hcount w) z * binaryInversions z +
      (N : ℝ) ^ 3 * Real.exp (θ * N / 2) * Real.exp (-(4 * t : ℝ) / (N : ℝ) ^ 3) /
        (Real.exp (-θ) ^ (N - 1) * (1 - Real.exp (-θ))) := by
  set h := hcount w with hhdef
  have hh : h ≤ N := hcount_le w
  set b := bot N h with hb
  have hρ0 : 0 < Real.exp (-θ) := Real.exp_pos _
  have hρ1 : Real.exp (-θ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hK : 0 < Real.exp (-θ) ^ (N - 1) * (1 - Real.exp (-θ)) :=
    mul_pos (pow_pos hρ0 _) (by linarith)
  set e : ℕ → ℕ → ℝ := fun t j =>
    ∑ z : BinaryWord N, (exclusionKernel N θ ^ t) b z * Real.exp (-θ) ^ pre z j -
      ∑ z : BinaryWord N, zeta θ h z * Real.exp (-θ) ^ pre z j with he
  have hbcl : hcount b = h := hcount_bot h hh
  have rowb : ∀ t, ∑ z, (exclusionKernel N θ ^ t) b z = 1 := fun t => kernel_pow_row hN θ t b
  have clb : ∀ t z, (exclusionKernel N θ ^ t) b z ≠ 0 → hcount z = h :=
    fun t z hz => (kernel_pow_class θ t b z hz).trans hbcl
  have he0 : ∀ t, e t 0 = 0 := by
    intro t; simp only [he, pre_zero, pow_zero, mul_one, rowb, zeta_sum θ h hh, sub_self]
  have heN : ∀ t, e t N = 0 := by
    intro t; simp only [he, pre_N]
    rw [sum_class_const _ h (rowb t) (clb t) (fun z => Real.exp (-θ) ^ hcount z)
        (Real.exp (-θ) ^ h) (fun z hz => by rw [hz]),
      sum_class_const _ h (zeta_sum θ h hh) (zeta_class θ h) (fun z => Real.exp (-θ) ^ hcount z)
        (Real.exp (-θ) ^ h) (fun z hz => by rw [hz]), sub_self]
  have hnn : ∀ t j, 0 ≤ e t j := by
    intro t j
    have hm : MonoW (fun z : BinaryWord N => -(Real.exp (-θ) ^ pre z j)) := by
      intro a z haz
      simp only [neg_le_neg_iff]
      exact pow_le_pow_of_le_one hρ0.le hρ1.le (haz j)
    have := stat_lower hN θ h hh t _ hm
    simp only [expectedAfter, mul_neg, Finset.sum_neg_distrib] at this
    simp only [he]; linarith
  have hinit : ∀ j, e 0 j ≤ 1 := by
    intro j
    have h1 : ∑ z, (exclusionKernel N θ ^ 0) b z * Real.exp (-θ) ^ pre z j =
        Real.exp (-θ) ^ pre b j := by simp [Matrix.one_apply]
    have h2 : 0 ≤ ∑ z : BinaryWord N, zeta θ h z * Real.exp (-θ) ^ pre z j :=
      Finset.sum_nonneg (fun z _ => mul_nonneg (zeta_nonneg θ h z) (pow_nonneg hρ0.le _))
    have h3 : Real.exp (-θ) ^ pre b j ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
    simp only [he]; rw [h1]; linarith
  have hrec : ∀ t j, 1 ≤ j → j ≤ N - 1 →
      e (t + 1) j ≤ (1 - 1 / ((N - 1 : ℕ) : ℝ)) * e t j +
        (1 / ((N - 1 : ℕ) : ℝ)) *
          (Real.exp (-θ) / (1 + Real.exp (-θ)) * e t (j - 1) +
            1 / (1 + Real.exp (-θ)) * e t (j + 1)) := by
    intro t j hj1 hjN
    have hA : ∑ z, (exclusionKernel N θ ^ (t + 1)) b z * Real.exp (-θ) ^ pre z j =
        ∑ y, (exclusionKernel N θ ^ t) b y *
          ∑ z, exclusionKernel N θ y z * Real.exp (-θ) ^ pre z j := by
      simp only [pow_succ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    have hZ : ∑ z : BinaryWord N, zeta θ h z * Real.exp (-θ) ^ pre z j =
        ∑ y : BinaryWord N, zeta θ h y * ∑ z, exclusionKernel N θ y z * Real.exp (-θ) ^ pre z j := by
      have := zeta_stationary hN θ h hh 1 (fun z => Real.exp (-θ) ^ pre z j)
      simp only [expectedAfter, pow_one] at this
      exact this.symm
    have hA' := hA.trans (rho_avg hN θ j hj1 hjN _)
    have hZ' := hZ.trans (rho_avg hN θ j hj1 hjN _)
    simp only [he]
    apply le_of_eq; linear_combination hA' - hZ'
  have hcon := contraction N hN θ hθ e he0 heN hnn hinit hrec t
  have hdomj : ∀ j, ∑ z : BinaryWord N, zeta θ h z * (pre z j : ℝ) -
      ∑ z, (exclusionKernel N θ ^ t) b z * (pre z j : ℝ) ≤
      e t j / (Real.exp (-θ) ^ (N - 1) * (1 - Real.exp (-θ))) := by
    intro j
    apply dominance (fun z => (exclusionKernel N θ ^ t) b z) (zeta θ h)
      (kernel_pow_nonneg θ t b) (zeta_nonneg θ h) (by rw [rowb, zeta_sum θ h hh])
      (fun z => pre z j) N (by omega) (fun z => pre_le z j) (Real.exp (-θ)) hρ0 hρ1
    intro m
    have hm : MonoW (fun z : BinaryWord N => if m ≤ pre z j then (1 : ℝ) else 0) := by
      intro a z haz
      have hj := haz j
      show (if m ≤ pre a j then (1 : ℝ) else 0) ≤ (if m ≤ pre z j then 1 else 0)
      by_cases h1 : m ≤ pre a j
      · rw [if_pos h1, if_pos (le_trans h1 hj)]
      · rw [if_neg h1]; split_ifs <;> norm_num
    exact stat_lower hN θ h hh t _ hm
  have hcmp : ∀ j, ∑ z, (exclusionKernel N θ ^ t) b z * (pre z j : ℝ) ≤
      ∑ z, (exclusionKernel N θ ^ t) w z * (pre z j : ℝ) := fun j =>
    expectedAfter_mono θ t (fun z => (pre z j : ℝ)) (fun a z haz => by show (pre a j : ℝ) ≤ pre z j; exact_mod_cast haz j)
      b w (bot_le w)
  have hw := inv_affine (fun z => (exclusionKernel N θ ^ t) w z) h hh (kernel_pow_row hN θ t w)
    (fun z hz => kernel_pow_class θ t w z hz)
  have hzV := inv_affine (zeta θ h) h hh (zeta_sum θ h hh) (zeta_class θ h)
  have hsum : ∑ j ∈ Finset.range N, (∑ z : BinaryWord N, zeta θ h z * (pre z j : ℝ) -
      ∑ z, (exclusionKernel N θ ^ t) w z * (pre z j : ℝ)) ≤
      (∑ j ∈ Finset.range N, e t j) / (Real.exp (-θ) ^ (N - 1) * (1 - Real.exp (-θ))) := by
    rw [Finset.sum_div]; apply Finset.sum_le_sum; intro j _
    linarith [hdomj j, hcmp j]
  have hdiv := div_le_div_of_nonneg_right hcon hK.le
  have hsplit : ∑ j ∈ Finset.range N, ((pre b j : ℝ) -
      ∑ z, (exclusionKernel N θ ^ t) w z * (pre z j : ℝ)) =
      ∑ j ∈ Finset.range N, ((pre b j : ℝ) - ∑ z : BinaryWord N, zeta θ h z * (pre z j : ℝ)) +
      ∑ j ∈ Finset.range N, (∑ z : BinaryWord N, zeta θ h z * (pre z j : ℝ) -
        ∑ z, (exclusionKernel N θ ^ t) w z * (pre z j : ℝ)) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intros; ring
  unfold expectedAfter
  rw [hw, hzV, hsplit]
  linarith

lemma numerics (n N : ℕ) (hn : 1024 ≤ n) (hN : 2 ≤ N) (hNn : N ≤ n) (θ : ℝ)
    (hθ1 : 1 / (2 * (n : ℝ)) < θ) (hθcap : θ ≤ 1 / 2) :
    (N : ℝ) ^ 3 * Real.exp (θ * N / 2) * Real.exp (-(4 * ((n ^ 4 : ℕ) : ℝ) : ℝ) / (N : ℝ) ^ 3) /
        (Real.exp (-θ) ^ (N - 1) * (1 - Real.exp (-θ))) ≤ 1 / 4 := by
  have hx : (1024 : ℝ) ≤ n := by exact_mod_cast hn
  have hy2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hyx : (N : ℝ) ≤ n := by exact_mod_cast hNn
  set x : ℝ := (n : ℝ) with hxdef
  set y : ℝ := (N : ℝ) with hydef
  have hθ0 : 0 < θ := lt_of_le_of_lt (by positivity) hθ1
  push_cast
  -- lower bound on the denominator
  have hu : Real.exp (-θ) * (1 + θ) ≤ 1 := by
    have h1 := Real.add_one_le_exp θ
    have h2 : Real.exp (-θ) * Real.exp θ = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-θ)]
  have hgap : θ / 2 ≤ 1 - Real.exp (-θ) := by
    by_cases hc : 1 / 2 ≤ Real.exp (-θ)
    · nlinarith
    · have hc := not_le.mp hc; linarith
  have hpow : Real.exp (-(θ * y)) ≤ Real.exp (-θ) ^ (N - 1) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have : ((N - 1 : ℕ) : ℝ) ≤ y := by rw [hydef]; exact_mod_cast Nat.sub_le N 1
    nlinarith
  have hD : Real.exp (-(θ * y)) * (θ / 2) ≤ Real.exp (-θ) ^ (N - 1) * (1 - Real.exp (-θ)) :=
    mul_le_mul hpow hgap (by positivity) (pow_nonneg (Real.exp_pos _).le _)
  have hDpos : 0 < Real.exp (-(θ * y)) * (θ / 2) := by positivity
  -- exponent bound
  have h4 : 4 * x ≤ 4 * x ^ 4 / y ^ 3 := by
    have hy3 : y ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by linarith) hyx 3
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hy3 (by positivity : (0 : ℝ) ≤ 4 * x)]
  have hθy : θ * y ≤ x / 2 := by nlinarith
  have hE : Real.exp (θ * y / 2) * Real.exp (-(4 * x ^ 4) / y ^ 3) ≤
      Real.exp (-(θ * y)) * Real.exp (-(3 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [neg_div]
    linarith
  -- 16 x^4 ≤ exp (3x)
  have hexp : 16 * x ^ 4 ≤ Real.exp (3 * x) := by
    have := Real.pow_div_factorial_le_exp (x := 3 * x) (by positivity) 5
    norm_num [Nat.factorial] at this
    have h5 : 16 * x ^ 4 ≤ (3 * x) ^ 5 / 120 := by
      nlinarith [mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ x) 4)
        (by linarith : (0 : ℝ) ≤ 243 * x - 1920)]
    linarith
  have hx3 : x ^ 3 * Real.exp (-(3 * x)) ≤ θ / 8 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    have hθx : 1 ≤ 2 * x * θ := by
      rw [div_lt_iff₀ (by positivity)] at hθ1; linarith
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ x) 3]
  have hy3 : y ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by linarith) hyx 3
  have hnum : y ^ 3 * Real.exp (θ * y / 2) * Real.exp (-(4 * x ^ 4) / y ^ 3) ≤
      Real.exp (-(θ * y)) * (θ / 2) / 4 := by
    calc y ^ 3 * Real.exp (θ * y / 2) * Real.exp (-(4 * x ^ 4) / y ^ 3)
        = y ^ 3 * (Real.exp (θ * y / 2) * Real.exp (-(4 * x ^ 4) / y ^ 3)) := by ring
      _ ≤ x ^ 3 * (Real.exp (-(θ * y)) * Real.exp (-(3 * x))) :=
          mul_le_mul hy3 hE (by positivity) (by positivity)
      _ = Real.exp (-(θ * y)) * (x ^ 3 * Real.exp (-(3 * x))) := by ring
      _ ≤ Real.exp (-(θ * y)) * (θ / 8) :=
          mul_le_mul_of_nonneg_left hx3 (Real.exp_pos _).le
      _ = _ := by ring
  rw [div_le_iff₀ (lt_of_lt_of_le hDpos hD)]
  linarith

end TranspositionIID.Main.Dev.L32.PartG
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32.PartG
open TranspositionIID.Main TranspositionIID.Main.Dev.L32
theorem lemma_3_2_dev (n N : ℕ) (hn : 1024 ≤ n) (hN : 2 ≤ N) (hNn : N ≤ n)
    (θ : ℝ) (hθ : 0 < θ) (hθcap : θ ≤ 1 / 2) (w : BinaryWord N)
    (hL : ∃ i, w i = false) (hH : ∃ i, w i = true) :
    expectedAfter (exclusionKernel N θ) w (n ^ 4) binaryInversions ≤
      1 / 4 + Real.pi ^ 2 / (6 * θ ^ 2) := by
  by_cases hθs : θ ≤ 1 / (2 * (n : ℝ))
  · have hx : (1024 : ℝ) ≤ n := by exact_mod_cast hn
    have hyx : (N : ℝ) ≤ n := by exact_mod_cast hNn
    have h1 : expectedAfter (exclusionKernel N θ) w (n ^ 4) binaryInversions ≤
        (N : ℝ) ^ 2 / 4 := by
      unfold expectedAfter
      calc ∑ z, (exclusionKernel N θ ^ (n ^ 4)) w z * binaryInversions z
          ≤ ∑ z, (exclusionKernel N θ ^ (n ^ 4)) w z * ((N : ℝ) ^ 2 / 4) :=
            Finset.sum_le_sum (fun z _ =>
              mul_le_mul_of_nonneg_left (inversions_le z) (kernel_pow_nonneg θ _ w z))
        _ = (N : ℝ) ^ 2 / 4 := by rw [← Finset.sum_mul, kernel_pow_row hN θ, one_mul]
    have h2 : (N : ℝ) ^ 2 / 4 ≤ Real.pi ^ 2 / (6 * θ ^ 2) := by
      have hxθ : 2 * (n : ℝ) * θ ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at hθs; linarith
      have hyθ : (N : ℝ) * θ ≤ 1 / 2 := by nlinarith
      have hyθ0 : 0 ≤ (N : ℝ) * θ := by positivity
      have hpi := Real.pi_gt_three
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [mul_le_mul hyθ hyθ hyθ0 (by norm_num)]
    linarith
  · replace hθs := not_le.mp hθs
    have hg := gap_bound hN θ hθ w (n ^ 4)
    have hz := zeta_inversions θ hθ (hcount w) (hcount_le w)
    have hnum := numerics n N hn hN hNn θ hθs hθcap
    linarith

end TranspositionIID.Main.Dev.L32.PartG
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
/-! ### Assembly -/
alias lemma_3_2_dev := TranspositionIID.Main.Dev.L32.PartG.lemma_3_2_dev

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false
open TranspositionIID
open TranspositionIID.Main
open TranspositionIID.Main.Dev
open TranspositionIID.Main.Dev.L32
open TranspositionIID.Main
variable {N : ℕ}
theorem solution (n N : ℕ) (hn : 1024 ≤ n) (hN : 2 ≤ N) (hNn : N ≤ n)
    (θ : ℝ) (hθ : 0 < θ) (hθcap : θ ≤ 1 / 2) (w : BinaryWord N)
    (hL : ∃ i, w i = false) (hH : ∃ i, w i = true) :
    expectedAfter (exclusionKernel N θ) w (n ^ 4) binaryInversions ≤
      1 / 4 + Real.pi ^ 2 / (6 * θ ^ 2) := by
  exact TranspositionIID.Main.Dev.L32.lemma_3_2_dev n N hn hN hNn θ hθ hθcap w hL hH
end
