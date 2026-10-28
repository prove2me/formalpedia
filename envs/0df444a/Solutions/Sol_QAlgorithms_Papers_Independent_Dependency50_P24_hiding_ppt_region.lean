-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.hiding_ppt_region
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:55:23.436992+00:00
-- url     : https://prove2.me/submissions/9c3c92bc-b826-4844-a0cb-37bd0c2b3ec1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
noncomputable section
namespace QAlgorithms.Papers.Independent.Dependency50.P24
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)
open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)
open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

namespace A3HP

/-- swap trace -/
def tau {I : Type*} [Fintype I] (h : Op (I × I)) : ℂ := ∑ s, ∑ u, h (s, u) (u, s)

theorem prodsum {k : ℕ} {I J : Type*} [Fintype I] [Fintype J] (g : I → J → ℂ) :
    ∑ s : Fin k → I, ∑ u : Fin k → J, ∏ t, g (s t) (u t) = (∑ x, ∑ y, g x y) ^ k := by
  have h1 : ∀ s : Fin k → I, ∑ u : Fin k → J, ∏ t, g (s t) (u t) = ∏ t, ∑ y, g (s t) y := by
    intro s
    rw [Fintype.prod_sum (fun t y => g (s t) y)]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun _ x => ∑ y, g x y)]
  simp

theorem copies_tau {I : Type*} [Fintype I] (ρ : Op (I × I)) (k : ℕ) :
    tau (bipartiteCopies ρ k) = tau ρ ^ k := by
  unfold tau bipartiteCopies
  exact prodsum (fun x y => ρ (x, y) (y, x))

theorem copies_trace {I J : Type*} [Fintype I] [Fintype J] (ρ : Op (I × J)) (k : ℕ) :
    (bipartiteCopies ρ k).trace = ρ.trace ^ k := by
  unfold bipartiteCopies Matrix.trace Matrix.diag
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  exact prodsum (fun x y => ρ (x, y) (x, y))

theorem copies_psd {I J : Type*} [Fintype I] [Fintype J] (ρ : Op (I × J)) (hρ : ρ.PosSemidef)
    (k : ℕ) : (bipartiteCopies ρ k).PosSemidef := by
  obtain ⟨M, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hρ
  let w : (Fin k → Fin M) → ((Fin k → I) × (Fin k → J)) → ℂ :=
    fun f a => ∏ t, v (f t) (a.1 t, a.2 t)
  have : bipartiteCopies ρ k = ∑ f, Matrix.vecMulVec (w f) (star (w f)) := by
    ext a b
    simp only [bipartiteCopies, hv, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      w, star_prod]
    rw [Fintype.prod_sum (fun t m => v m (a.1 t, a.2 t) * star (v m (b.1 t, b.2 t)))]
    simp [Finset.prod_mul_distrib]
  rw [this]
  exact Matrix.posSemidef_sum _ fun f _ => Matrix.posSemidef_vecMulVec_self_star _

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

theorem swap_apply {d : ℕ} (a b : Fin d × Fin d) :
    (swapMatrix (I := Fin d)) a b = if b = (a.2, a.1) then 1 else 0 := by
  unfold QAlgorithms.Papers.Independent.Information100.P76.swapMatrix
  by_cases h : b = (a.2, a.1)
  · subst h; simp
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2⟩
    exact h (Prod.ext h2.symm h1.symm)

theorem swap_mul {d : ℕ} : (swapMatrix (I := Fin d)) * (swapMatrix (I := Fin d)) = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (a.2, a.1)]
  · rw [swap_apply, if_pos rfl, one_mul, swap_apply, Matrix.one_apply]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg h, if_neg]
      intro h'; apply h; rw [h']
  · intro x _ hx; rw [swap_apply, if_neg hx, zero_mul]
  · simp

theorem swap_herm {d : ℕ} : (swapMatrix (I := Fin d))ᴴ = swapMatrix (I := Fin d) := by
  ext a b
  rw [Matrix.conjTranspose_apply, swap_apply, swap_apply]
  by_cases h : b = (a.2, a.1)
  · subst h; simp
  · rw [if_neg, if_neg h]
    · simp
    · intro h'; apply h; rw [h']

theorem one_pm_psd {d : ℕ} (c : ℂ) (hc : c * c = 1) (hcs : star c = c) :
    ((1 : Op (Fin d × Fin d)) + c • swapMatrix (I := Fin d)).PosSemidef := by
  have hsq : (1 + c • swapMatrix (I := Fin d)) * (1 + c • swapMatrix (I := Fin d)) =
      (2 : ℂ) • (1 + c • swapMatrix (I := Fin d)) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, smul_mul_smul_comm, hc, swap_mul, one_smul, two_smul]
    abel
  have : (1 : Op (Fin d × Fin d)) + c • swapMatrix (I := Fin d) =
      ((1 / 2 : ℝ) : ℂ) • ((1 + c • swapMatrix (I := Fin d))ᴴ * (1 + c • swapMatrix (I := Fin d))) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, swap_herm,
      hcs, hsq, smul_smul]
    norm_num
  rw [this]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).smul
    (by exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 2))

theorem tau_one {d : ℕ} : tau (1 : Op (Fin d × Fin d)) = d := by
  unfold tau
  simp [Matrix.one_apply, Prod.ext_iff, eq_comm]

theorem tau_swap {d : ℕ} : tau (swapMatrix (I := Fin d)) = (d : ℂ) ^ 2 := by
  unfold tau
  simp [swap_apply, sq]

theorem trace_swap {d : ℕ} : (swapMatrix (I := Fin d)).trace = d := by
  unfold Matrix.trace Matrix.diag
  rw [Fintype.sum_prod_type]
  have : ∀ x : Fin d, ∑ y : Fin d, (swapMatrix (I := Fin d)) (x, y) (x, y) = 1 := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp [swap_apply]
    · intro y _ hy
      rw [swap_apply, if_neg]
      intro h
      exact hy (Prod.mk.inj h).1.symm
    · simp
  simp [this]

theorem tau_add {I : Type*} [Fintype I] (A B : Op (I × I)) : tau (A + B) = tau A + tau B := by
  simp [tau, Finset.sum_add_distrib]

theorem tau_sub {I : Type*} [Fintype I] (A B : Op (I × I)) : tau (A - B) = tau A - tau B := by
  simp [tau, Finset.sum_sub_distrib]

theorem tau_smul {I : Type*} [Fintype I] (c : ℂ) (A : Op (I × I)) : tau (c • A) = c * tau A := by
  simp [tau, Finset.mul_sum]

theorem sym_facts {d : ℕ} (hd : 2 ≤ d) :
    (symmetricWerner d).PosSemidef ∧ (symmetricWerner d).trace = 1 ∧ tau (symmetricWerner d) = 1 := by
  have hd0 : ((d : ℂ) ^ 2 + d) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) ^ 2 + d := by positivity
    exact_mod_cast this.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold symmetricWerner
    have := one_pm_psd (d := d) 1 (by simp) (by simp)
    rw [one_smul] at this
    refine this.smul ?_
    have e : ((d : ℂ) ^ 2 + d)⁻¹ = ((((d : ℝ) ^ 2 + d)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    have : (0 : ℝ) ≤ ((d : ℝ) ^ 2 + d)⁻¹ := by positivity
    exact_mod_cast this
  · unfold symmetricWerner
    rw [Matrix.trace_smul, Matrix.trace_add, trace_swap, Matrix.trace_one]
    simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
    push_cast
    linear_combination inv_mul_cancel₀ hd0
  · unfold symmetricWerner
    rw [tau_smul, tau_add, tau_one, tau_swap]
    linear_combination inv_mul_cancel₀ hd0

theorem anti_facts {d : ℕ} (hd : 2 ≤ d) :
    (antisymmetricWerner d).PosSemidef ∧ (antisymmetricWerner d).trace = 1 ∧
      tau (antisymmetricWerner d) = -1 := by
  have hdr : (0 : ℝ) < (d : ℝ) ^ 2 - d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hd0 : ((d : ℂ) ^ 2 - d) ≠ 0 := by exact_mod_cast hdr.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold antisymmetricWerner
    have := one_pm_psd (d := d) (-1) (by simp) (by simp)
    rw [neg_one_smul, ← sub_eq_add_neg] at this
    refine this.smul ?_
    have e : ((d : ℂ) ^ 2 - d)⁻¹ = ((((d : ℝ) ^ 2 - d)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    have : (0 : ℝ) ≤ ((d : ℝ) ^ 2 - d)⁻¹ := by positivity
    exact_mod_cast this
  · unfold antisymmetricWerner
    rw [Matrix.trace_smul, Matrix.trace_sub, trace_swap, Matrix.trace_one]
    simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
    push_cast
    linear_combination inv_mul_cancel₀ hd0
  · unfold antisymmetricWerner
    rw [tau_smul, tau_sub, tau_one, tau_swap]
    linear_combination -(inv_mul_cancel₀ hd0)

theorem sqrt2_sq : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

theorem bell_psd (odd minus : Bool) : (signedBell odd minus).PosSemidef := by
  unfold signedBell
  have := Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp (WithLp.toLp 2 fun a : Key 2 =>
    if (if odd then a.1 ≠ a.2 else a.1 = a.2) then
      (if minus = true ∧ a.1 = 1 then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) else 0))
  convert this using 1
  ext i j
  simp [pureDensity, Matrix.vecMulVec_apply]

theorem bell_trace (odd minus : Bool) : (signedBell odd minus).trace = 1 := by
  cases odd <;> cases minus <;>
    simp [signedBell, pureDensity, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two,
      sqrt2_sq] <;> norm_num

def bsum (β : Op (Key 2)) : ℂ := ∑ i, ∑ j, β (i, j) (j, i)

theorem bsum_ff : bsum (signedBell false false) = 1 := by
  simp [bsum, signedBell, pureDensity, Fin.sum_univ_two, sqrt2_sq]
theorem bsum_ft : bsum (signedBell false true) = 1 := by
  simp [bsum, signedBell, pureDensity, Fin.sum_univ_two, sqrt2_sq] <;> norm_num
theorem bsum_tf : bsum (signedBell true false) = 1 := by
  simp [bsum, signedBell, pureDensity, Fin.sum_univ_two, sqrt2_sq] <;> norm_num
theorem bsum_tt : bsum (signedBell true true) = -1 := by
  simp [bsum, signedBell, pureDensity, Fin.sum_univ_two, sqrt2_sq] <;> norm_num

theorem paired_psd {S T : Type*} [Fintype S] [Fintype T] (A B : Op (S × T))
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (pairedFlags A B).PosSemidef := by
  have := (hA.kronecker hB).submatrix
    (fun a : (S × S) × (T × T) => ((a.1.1, a.2.1), (a.1.2, a.2.2)))
  exact this

theorem paired_trace {S T : Type*} [Fintype S] [Fintype T] (A B : Op (S × T)) :
    (pairedFlags A B).trace = A.trace * B.trace := by
  simp only [pairedFlags, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Finset.sum_mul_sum]

def wit {α β : Type*} : (α × α) × (β × β) → ℂ :=
  fun a => if a.1.1 = a.1.2 ∧ a.2.1 = a.2.2 then 1 else 0

theorem diag_sum {α β : Type*} [Fintype α] [Fintype β] (f : (α × α) × (β × β) → ℂ) :
    ∑ a, wit a * f a = ∑ i, ∑ p, f ((i, i), (p, p)) := by
  simp only [wit, Fintype.sum_prod_type, ite_and, ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_irrel, Finset.sum_ite_eq]

def Q {S : Type*} [Fintype S] (M : Op (Key 2 × ((S × S) × (S × S)))) : ℂ :=
  ∑ i, ∑ p, ∑ j, ∑ q, M ((i, j), (p, q)) ((j, i), (q, p))

theorem witness {S : Type*} [Fintype S] (M : Op (Key 2 × ((S × S) × (S × S)))) :
    star wit ⬝ᵥ (transposeBob M *ᵥ wit) = Q M := by
  have hx : star (wit (α := Fin 2) (β := S × S)) = wit := by
    funext a; simp only [Pi.star_apply, wit]; split_ifs <;> simp
  rw [hx]
  unfold dotProduct Matrix.mulVec
  simp only [dotProduct]
  have h1 : ∀ a, (∑ b, transposeBob M a b * wit b) = ∑ j, ∑ q, transposeBob M a ((j, j), (q, q)) := by
    intro a
    simp_rw [mul_comm (transposeBob M a _)]
    exact diag_sum (fun b => transposeBob M a b)
  simp_rw [h1]
  exact diag_sum (fun a => ∑ j, ∑ q, transposeBob M a ((j, j), (q, q)))

theorem Q_add {S : Type*} [Fintype S] (M N : Op (Key 2 × ((S × S) × (S × S)))) :
    Q (M + N) = Q M + Q N := by
  simp [Q, Finset.sum_add_distrib]

theorem Q_smul {S : Type*} [Fintype S] (c : ℂ) (M : Op (Key 2 × ((S × S) × (S × S)))) :
    Q (c • M) = c * Q M := by
  simp only [Q, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem tk {m n : Type*} [Fintype m] [Fintype n] (A : Op m) (B : Op n) :
    (Matrix.kronecker A B).trace = A.trace * B.trace := Matrix.trace_kronecker A B

theorem half_nonneg' : (0 : ℂ) ≤ 1 / 2 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
  exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem quarter_nonneg' : (0 : ℂ) ≤ 1 / 4 := by
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring]
  exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 4)

theorem Q_kron {S : Type*} [Fintype S] (β : Op (Key 2)) (A B : Op (S × S)) :
    Q (Matrix.kronecker β (pairedFlags A B)) = bsum β * (tau A * tau B) := by
  have inner : ∑ p : S × S, ∑ q : S × S, A (p.1, q.1) (q.1, p.1) * B (p.2, q.2) (q.2, p.2) =
      tau A * tau B := by
    simp only [tau, Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp only [Q, bsum, Matrix.kronecker, Matrix.kroneckerMap_apply, pairedFlags]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]


def KM (c : Key 2 → ℂ) : Op (Key 2) := Matrix.vecMulVec c (star c)

def wp : Key 2 → ℂ := fun a => if a = (0, 0) ∨ a = (1, 1) then 1 else 0
def wm : Key 2 → ℂ := fun a => if a = (0, 0) then 1 else if a = (1, 1) then -1 else 0
def e00 : Key 2 → ℂ := fun a => if a = (0, 0) then 1 else 0
def e11 : Key 2 → ℂ := fun a => if a = (1, 1) then 1 else 0
def e01 : Key 2 → ℂ := fun a => if a = (0, 1) then 1 else 0
def e10 : Key 2 → ℂ := fun a => if a = (1, 0) then 1 else 0
def vp : Key 2 → ℂ := fun a => if a = (0, 1) ∨ a = (1, 0) then 1 else 0
def vm : Key 2 → ℂ := fun a => if a = (0, 1) then 1 else if a = (1, 0) then -1 else 0

theorem decomp (p : ℝ) (d k : ℕ) :
    hidingFamily p d k =
      Matrix.kronecker (KM wp) (((p / 2 : ℝ) : ℂ) • hidingOne d k) +
      Matrix.kronecker (KM wm) (((p / 2 : ℝ) : ℂ) • hidingTwo d k) +
      Matrix.kronecker (KM e01) (((1 / 2 - p : ℝ) : ℂ) • hidingTwo d k) +
      Matrix.kronecker (KM e10) (((1 / 2 - p : ℝ) : ℂ) • hidingTwo d k) := by
  ext ⟨⟨a1, a2⟩, s⟩ ⟨⟨b1, b2⟩, s'⟩
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [hidingFamily, KM, wp, wm, e01, e10, Matrix.kronecker, Matrix.vecMulVec_apply] <;> ring

theorem decompT (p : ℝ) (d k : ℕ) :
    transposeBob (hidingFamily p d k) =
      Matrix.kronecker (KM e00) (((p / 2 : ℝ) : ℂ) • (transposeSecond (hidingOne d k) +
        transposeSecond (hidingTwo d k))) +
      Matrix.kronecker (KM e11) (((p / 2 : ℝ) : ℂ) • (transposeSecond (hidingOne d k) +
        transposeSecond (hidingTwo d k))) +
      Matrix.kronecker (KM vp) ((1 / 2 : ℂ) • (((1 / 2 - p : ℝ) : ℂ) • transposeSecond (hidingTwo d k) +
        ((p / 2 : ℝ) : ℂ) • (transposeSecond (hidingOne d k) - transposeSecond (hidingTwo d k)))) +
      Matrix.kronecker (KM vm) ((1 / 2 : ℂ) • (((1 / 2 - p : ℝ) : ℂ) • transposeSecond (hidingTwo d k) -
        ((p / 2 : ℝ) : ℂ) • (transposeSecond (hidingOne d k) - transposeSecond (hidingTwo d k)))) := by
  ext ⟨⟨a1, a2⟩, s⟩ ⟨⟨b1, b2⟩, s'⟩
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [transposeBob, transposeSecond, hidingFamily, KM, e00, e11, vp, vm, Matrix.kronecker,
      Matrix.vecMulVec_apply] <;> ring

/-! ### Partial transpose of Werner states -/

def φd (d : ℕ) : Fin d × Fin d → ℂ := fun a => if a.1 = a.2 then 1 else 0

def Pm (d : ℕ) : Op (Fin d × Fin d) := ((d : ℂ)⁻¹) • Matrix.vecMulVec (φd d) (star (φd d))

def Qm (d : ℕ) : Op (Fin d × Fin d) := 1 - Pm d

theorem Pm_apply {d : ℕ} (a b : Fin d × Fin d) :
    Pm d a b = (d : ℂ)⁻¹ * ((if a.1 = a.2 then 1 else 0) * (if b.1 = b.2 then 1 else 0)) := by
  simp [Pm, φd, Matrix.vecMulVec_apply]

theorem sum_diag_one {d : ℕ} : ∑ c : Fin d × Fin d, (if c.1 = c.2 then (1 : ℂ) else 0) = d := by
  rw [Fintype.sum_prod_type]; simp

theorem Pm_psd {d : ℕ} : (Pm d).PosSemidef := by
  unfold Pm
  refine (Matrix.posSemidef_vecMulVec_self_star _).smul ?_
  have : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
  have e : ((d : ℂ)⁻¹) = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [e]; exact_mod_cast this

theorem Pm_herm {d : ℕ} : (Pm d)ᴴ = Pm d := (Pm_psd).1.eq

theorem Pm_mul {d : ℕ} (hd : 2 ≤ d) : Pm d * Pm d = Pm d := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  ext a b
  rw [Matrix.mul_apply]
  simp_rw [Pm_apply]
  have : ∀ c : Fin d × Fin d, (d : ℂ)⁻¹ * ((if a.1 = a.2 then 1 else 0) * (if c.1 = c.2 then 1 else 0)) *
      ((d : ℂ)⁻¹ * ((if c.1 = c.2 then 1 else 0) * (if b.1 = b.2 then 1 else 0))) =
      ((d : ℂ)⁻¹ * (d : ℂ)⁻¹ * ((if a.1 = a.2 then 1 else 0) * (if b.1 = b.2 then 1 else 0))) *
        (if c.1 = c.2 then (1 : ℂ) else 0) := by
    intro c; split_ifs <;> ring
  simp_rw [this]
  rw [← Finset.mul_sum, sum_diag_one]
  field_simp

theorem Qm_psd {d : ℕ} (hd : 2 ≤ d) : (Qm d).PosSemidef := by
  have h : Qm d = (Qm d)ᴴ * Qm d := by
    unfold Qm
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Pm_herm, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Pm_mul hd]
    abel
  rw [h]; exact Matrix.posSemidef_conjTranspose_mul_self _

theorem Γ_one {d : ℕ} : transposeSecond (1 : Op (Fin d × Fin d)) = 1 := by
  ext a b
  simp only [transposeSecond, Matrix.one_apply, Prod.ext_iff]
  by_cases h1 : a.1 = b.1 <;> by_cases h2 : a.2 = b.2 <;> simp [h1, h2, eq_comm]

theorem Γ_swap {d : ℕ} (hd : 2 ≤ d) :
    transposeSecond (swapMatrix (I := Fin d)) = (d : ℂ) • Pm d := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  ext a b
  simp only [transposeSecond, swap_apply, Matrix.smul_apply, Pm_apply, smul_eq_mul, Prod.ext_iff]
  rw [← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
  by_cases h1 : a.1 = a.2 <;> by_cases h2 : b.1 = b.2 <;> simp [h1, h2, eq_comm]

theorem Γ_add {S T : Type*} (A B : Op (S × T)) :
    transposeSecond (A + B) = transposeSecond A + transposeSecond B := rfl
theorem Γ_sub {S T : Type*} (A B : Op (S × T)) :
    transposeSecond (A - B) = transposeSecond A - transposeSecond B := rfl
theorem Γ_smul {S T : Type*} (c : ℂ) (A : Op (S × T)) :
    transposeSecond (c • A) = c • transposeSecond A := rfl

def cs (d : ℕ) : ℝ := ((d : ℝ) ^ 2 + d)⁻¹
def ca (d : ℕ) : ℝ := ((d : ℝ) ^ 2 - d)⁻¹

theorem Γ_sym {d : ℕ} (hd : 2 ≤ d) :
    transposeSecond (symmetricWerner d) = (cs d : ℂ) • Qm d + ((cs d * (1 + d) : ℝ) : ℂ) • Pm d := by
  unfold symmetricWerner
  rw [Γ_smul, Γ_add, Γ_one, Γ_swap hd, show ((d : ℂ) ^ 2 + d)⁻¹ = (cs d : ℂ) by simp [cs]]
  unfold Qm
  push_cast
  module

theorem Γ_anti {d : ℕ} (hd : 2 ≤ d) :
    transposeSecond (antisymmetricWerner d) = (ca d : ℂ) • Qm d + ((ca d * (1 - d) : ℝ) : ℂ) • Pm d := by
  unfold antisymmetricWerner
  rw [Γ_smul, Γ_sub, Γ_one, Γ_swap hd, show ((d : ℂ) ^ 2 - d)⁻¹ = (ca d : ℂ) by simp [ca]]
  unfold Qm
  push_cast
  module

def x0 (d : ℕ) : ℝ := (cs d + ca d) / 2

theorem coef_cancel {d : ℕ} (hd : 2 ≤ d) : cs d * (1 + d) + ca d * (1 - d) = 0 := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (d : ℝ) ^ 2 + d ≠ 0 := by positivity
  have h3 : (d : ℝ) ^ 2 - d ≠ 0 := by nlinarith
  have h4 : (d : ℝ) - 1 ≠ 0 := by linarith
  have h5 : (d : ℝ) + 1 ≠ 0 := by linarith
  unfold cs ca
  field_simp
  ring

theorem Γ_base {d : ℕ} (hd : 2 ≤ d) :
    transposeSecond ((1 / 2 : ℂ) • (symmetricWerner d + antisymmetricWerner d)) =
      (x0 d : ℂ) • Qm d := by
  rw [Γ_smul, Γ_add, Γ_sym hd, Γ_anti hd]
  have hc := coef_cancel hd
  have : ((cs d * (1 + d) : ℝ) : ℂ) = -((ca d * (1 - d) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg]; congr 1; linarith
  rw [this]
  unfold x0
  push_cast
  module

theorem cs_pos {d : ℕ} (hd : 2 ≤ d) : 0 < cs d := by unfold cs; positivity
theorem ca_pos {d : ℕ} (hd : 2 ≤ d) : 0 < ca d := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold ca
  have : 0 < (d : ℝ) ^ 2 - d := by nlinarith
  positivity
theorem x0_pos {d : ℕ} (hd : 2 ≤ d) : 0 < x0 d := by
  unfold x0; linarith [cs_pos hd, ca_pos hd]

theorem ratio {d : ℕ} (hd : 2 ≤ d) : x0 d = cs d * ((d : ℝ) / (d - 1)) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (d : ℝ) ^ 2 + d ≠ 0 := by positivity
  have h3 : (d : ℝ) ^ 2 - d ≠ 0 := by nlinarith
  have h4 : (d : ℝ) - 1 ≠ 0 := by linarith
  have h5 : (d : ℝ) + 1 ≠ 0 := by linarith
  have h6 : (d : ℝ) ≠ 0 := by linarith
  unfold x0 cs ca
  field_simp
  ring

theorem cofp {r : ℝ} (hr : 0 ≤ r) : (0 : ℂ) ≤ (r : ℂ) := by exact_mod_cast hr

/-! ### Variable tensor products -/

def copiesVar {I J : Type*} {k : ℕ} (M : Fin k → Op (I × J)) : Op ((Fin k → I) × (Fin k → J)) :=
  fun a b => ∏ t, M t (a.1 t, a.2 t) (b.1 t, b.2 t)

theorem copiesVar_psd {I J : Type*} [Fintype I] [Fintype J] {k : ℕ} (M : Fin k → Op (I × J))
    (h : ∀ t, (M t).PosSemidef) : (copiesVar M).PosSemidef := by
  choose m v hv using fun t => Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (h t)
  let w : ((t : Fin k) → Fin (m t)) → ((Fin k → I) × (Fin k → J)) → ℂ :=
    fun f a => ∏ t, v t (f t) (a.1 t, a.2 t)
  have : copiesVar M = ∑ f, Matrix.vecMulVec (w f) (star (w f)) := by
    ext a b
    simp only [copiesVar, hv, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, w, star_prod]
    rw [Fintype.prod_sum (fun t j => v t j (a.1 t, a.2 t) * star (v t j (b.1 t, b.2 t)))]
    simp [Finset.prod_mul_distrib]
  rw [this]
  exact Matrix.posSemidef_sum _ fun f _ => Matrix.posSemidef_vecMulVec_self_star _

theorem copies_expand {I J : Type*} [Fintype I] [Fintype J] (k : ℕ) (a b : ℝ) (Q P : Op (I × J)) :
    bipartiteCopies ((a : ℂ) • Q + (b : ℂ) • P) k =
      ∑ f : Fin k → Bool, (((∏ t, if f t then b else a : ℝ)) : ℂ) •
        copiesVar (fun t => if f t then P else Q) := by
  ext x y
  simp only [bipartiteCopies, copiesVar, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sum_apply]
  have h : ∀ t, (a : ℂ) * Q (x.1 t, x.2 t) (y.1 t, y.2 t) + (b : ℂ) * P (x.1 t, x.2 t) (y.1 t, y.2 t) =
      ∑ j : Bool, ((if j then b else a : ℝ) : ℂ) *
        (if j then P else Q) (x.1 t, x.2 t) (y.1 t, y.2 t) := by
    intro t; simp [add_comm]
  simp_rw [h]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl

theorem copies_smul {I J : Type*} [Fintype I] [Fintype J] (k : ℕ) (c : ℂ) (Q : Op (I × J)) :
    bipartiteCopies (c • Q) k = c ^ k • copiesVar (fun _ : Fin k => Q) := by
  ext x y
  simp [bipartiteCopies, copiesVar, Finset.prod_mul_distrib]

/-! ### Quadratic forms -/

def Fm {n : Type*} [Fintype n] (φ : n → ℂ) (Z : Op n) : ℂ := star φ ⬝ᵥ (Z *ᵥ φ)

theorem F_add {n : Type*} [Fintype n] (φ : n → ℂ) (A B : Op n) : Fm φ (A + B) = Fm φ A + Fm φ B := by
  simp [Fm, Matrix.add_mulVec, dotProduct_add]
theorem F_sub {n : Type*} [Fintype n] (φ : n → ℂ) (A B : Op n) : Fm φ (A - B) = Fm φ A - Fm φ B := by
  simp [Fm, Matrix.sub_mulVec, dotProduct_sub]
theorem F_smul {n : Type*} [Fintype n] (φ : n → ℂ) (c : ℂ) (A : Op n) : Fm φ (c • A) = c * Fm φ A := by
  simp [Fm, Matrix.smul_mulVec, dotProduct_smul]

theorem kron_form {m n : Type*} [Fintype m] [Fintype n] (c : m → ℂ) (φ : n → ℂ) (K : Op m) (Z : Op n) :
    Fm (fun a : m × n => c a.1 * φ a.2) (Matrix.kronecker K Z) = Fm c K * Fm φ Z := by
  simp only [Fm, dotProduct, Matrix.mulVec, Pi.star_apply, star_mul', Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro t _
  ring

def φ1 {S : Type*} : S × S → ℂ := fun a => if a.1 = a.2 then 1 else 0

theorem F_φ1 {S : Type*} [Fintype S] (M : Op (S × S)) : Fm φ1 (transposeSecond M) = tau M := by
  have hx : star (φ1 (S := S)) = φ1 := by
    funext a; simp only [Pi.star_apply, φ1]; split_ifs <;> simp
  have key : ∀ g : S × S → ℂ, ∑ a, φ1 a * g a = ∑ s, g (s, s) := by
    intro g
    rw [Fintype.sum_prod_type]
    simp [φ1]
  simp only [Fm, hx, dotProduct, Matrix.mulVec]
  have h1 : ∀ a, (∑ b, transposeSecond M a b * φ1 b) = ∑ u, transposeSecond M a (u, u) := by
    intro a; simp_rw [mul_comm (transposeSecond M a _)]; exact key _
  simp_rw [h1]
  rw [key]
  rfl

theorem F_single {n : Type*} [Fintype n] [DecidableEq n] (a0 : n) (Z : Op n) :
    Fm (Pi.single a0 1) Z = Z a0 a0 := by
  simp [Fm]

theorem keyF : Fm vp (KM e00) = 0 ∧ Fm vp (KM e11) = 0 ∧ Fm vp (KM vp) = 4 ∧ Fm vp (KM vm) = 0 ∧
    Fm vm (KM e00) = 0 ∧ Fm vm (KM e11) = 0 ∧ Fm vm (KM vp) = 0 ∧ Fm vm (KM vm) = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Fm, KM, vp, vm, e00, e11, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num


/-! ### Main argument -/

theorem KM_psd (c : Key 2 → ℂ) : (KM c).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _

def CQ (d k : ℕ) : Op ((Fin k → Fin d) × (Fin k → Fin d)) := copiesVar (fun _ : Fin k => Qm d)

theorem CQ_psd {d k : ℕ} (hd : 2 ≤ d) : (CQ d k).PosSemidef :=
  copiesVar_psd _ fun _ => Qm_psd hd

theorem A_eq {d k : ℕ} (hd : 2 ≤ d) :
    transposeSecond (hidingOne d k) = ((x0 d : ℂ)) ^ k • CQ d k := by
  have : transposeSecond (hidingOne d k) =
      bipartiteCopies (transposeSecond ((1 / 2 : ℂ) • (symmetricWerner d + antisymmetricWerner d))) k := rfl
  rw [this, Γ_base hd, copies_smul]; rfl

theorem B_eq {d k : ℕ} (hd : 2 ≤ d) :
    transposeSecond (hidingTwo d k) =
      ∑ f : Fin k → Bool, (((∏ t, if f t then cs d * (1 + d) else cs d : ℝ)) : ℂ) •
        copiesVar (fun t => if f t then Pm d else Qm d) := by
  have : transposeSecond (hidingTwo d k) =
      bipartiteCopies (transposeSecond (symmetricWerner d)) k := rfl
  rw [this, Γ_sym hd, copies_expand]

theorem B_rem {d k : ℕ} (hd : 2 ≤ d) :
    (transposeSecond (hidingTwo d k) - ((cs d : ℂ)) ^ k • CQ d k).PosSemidef := by
  rw [B_eq hd, ← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ => false))]
  have h0 : (((∏ t : Fin k, if (fun _ => false : Fin k → Bool) t then cs d * (1 + d) else cs d : ℝ)) : ℂ) •
        copiesVar (fun t => if (fun _ => false : Fin k → Bool) t then Pm d else Qm d) =
      ((cs d : ℂ)) ^ k • CQ d k := by
    simp [CQ]
  rw [h0, add_sub_cancel_left]
  refine Matrix.posSemidef_sum _ fun f _ => ?_
  refine (copiesVar_psd _ fun t => ?_).smul (cofp ?_)
  · by_cases h : f t
    · simp only [h, if_true]; exact Pm_psd
    · simp only [h]; exact Qm_psd hd
  · refine Finset.prod_nonneg fun t _ => ?_
    have := cs_pos hd
    split_ifs <;> positivity

theorem B_psd {d k : ℕ} (hd : 2 ≤ d) : (transposeSecond (hidingTwo d k)).PosSemidef := by
  have := (B_rem (k := k) hd).add ((CQ_psd (k := k) hd).smul (cofp (pow_nonneg (cs_pos hd).le k)))
  rw [Complex.ofReal_pow, sub_add_cancel] at this
  exact this

theorem A_psd {d k : ℕ} (hd : 2 ≤ d) : (transposeSecond (hidingOne d k)).PosSemidef := by
  rw [A_eq hd]
  have := (CQ_psd (k := k) hd).smul (cofp (pow_nonneg (x0_pos hd).le k))
  convert this using 2; push_cast; rfl

theorem decompT' (p : ℝ) (d k : ℕ) :
    transposeBob (hidingFamily p d k) =
      Matrix.kronecker (KM e00) (((p / 2 : ℝ) : ℂ) • (transposeSecond (hidingOne d k) +
        transposeSecond (hidingTwo d k))) +
      Matrix.kronecker (KM e11) (((p / 2 : ℝ) : ℂ) • (transposeSecond (hidingOne d k) +
        transposeSecond (hidingTwo d k))) +
      Matrix.kronecker (KM vp) ((((1 - 3 * p) / 4 : ℝ) : ℂ) • transposeSecond (hidingTwo d k) +
        ((p / 4 : ℝ) : ℂ) • transposeSecond (hidingOne d k)) +
      Matrix.kronecker (KM vm) ((1 / 4 : ℂ) • (((1 - p : ℝ) : ℂ) • transposeSecond (hidingTwo d k) -
        (p : ℂ) • transposeSecond (hidingOne d k))) := by
  have e3 : (1 / 2 : ℂ) • (((1 / 2 - p : ℝ) : ℂ) • transposeSecond (hidingTwo d k) +
        ((p / 2 : ℝ) : ℂ) • (transposeSecond (hidingOne d k) - transposeSecond (hidingTwo d k))) =
      (((1 - 3 * p) / 4 : ℝ) : ℂ) • transposeSecond (hidingTwo d k) +
        ((p / 4 : ℝ) : ℂ) • transposeSecond (hidingOne d k) := by
    push_cast; module
  have e4 : (1 / 2 : ℂ) • (((1 / 2 - p : ℝ) : ℂ) • transposeSecond (hidingTwo d k) -
        ((p / 2 : ℝ) : ℂ) • (transposeSecond (hidingOne d k) - transposeSecond (hidingTwo d k))) =
      (1 / 4 : ℂ) • (((1 - p : ℝ) : ℂ) • transposeSecond (hidingTwo d k) -
        (p : ℂ) • transposeSecond (hidingOne d k)) := by
    push_cast; module
  rw [decompT, e3, e4]

theorem ppt_of {d k : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 0 < p) (h3 : p ≤ 1 / 3)
    (hr : ((d : ℝ) / (d - 1)) ^ k ≤ (1 - p) / p) :
    (transposeBob (hidingFamily p d k)).PosSemidef := by
  rw [decompT']
  have hA := A_psd (k := k) hd
  have hB := B_psd (k := k) hd
  have hAB := hA.add hB
  have t1 := (KM_psd e00).kronecker (hAB.smul (cofp (by linarith : (0 : ℝ) ≤ p / 2)))
  have t2 := (KM_psd e11).kronecker (hAB.smul (cofp (by linarith : (0 : ℝ) ≤ p / 2)))
  have t3 := (KM_psd vp).kronecker ((hB.smul (cofp (by linarith : (0 : ℝ) ≤ (1 - 3 * p) / 4))).add
    (hA.smul (cofp (by linarith : (0 : ℝ) ≤ p / 4))))
  -- the delicate term
  have hcoef : 0 ≤ (1 - p) * cs d ^ k - p * x0 d ^ k := by
    rw [ratio hd, mul_pow]
    have h1 : p * ((d : ℝ) / (d - 1)) ^ k ≤ 1 - p := by
      rwa [le_div_iff₀ hp, mul_comm] at hr
    have h2 : 0 ≤ cs d ^ k := pow_nonneg (cs_pos hd).le k
    nlinarith
  have hD : (((1 - p : ℝ) : ℂ) • transposeSecond (hidingTwo d k) -
      (p : ℂ) • transposeSecond (hidingOne d k)) =
      ((1 - p : ℝ) : ℂ) • (transposeSecond (hidingTwo d k) - ((cs d : ℂ)) ^ k • CQ d k) +
      (((1 - p) * cs d ^ k - p * x0 d ^ k : ℝ) : ℂ) • CQ d k := by
    rw [A_eq hd]
    push_cast
    module
  have t4 : (((1 - p : ℝ) : ℂ) • transposeSecond (hidingTwo d k) -
      (p : ℂ) • transposeSecond (hidingOne d k)).PosSemidef := by
    rw [hD]
    exact ((B_rem hd).smul (cofp (by linarith))).add ((CQ_psd hd).smul (cofp hcoef))
  exact ((t1.add t2).add t3).add ((KM_psd vm).kronecker (t4.smul quarter_nonneg'))

theorem form_nonneg {n : Type*} [Fintype n] {M : Op n} (h : M.PosSemidef) (x : n → ℂ) :
    0 ≤ Fm x M := h.dotProduct_mulVec_nonneg x

theorem tau_base {d : ℕ} (hd : 2 ≤ d) :
    tau ((1 / 2 : ℂ) • (symmetricWerner d + antisymmetricWerner d)) = 0 := by
  rw [tau_smul, tau_add, (sym_facts hd).2.2, (anti_facts hd).2.2]; ring

theorem cond1 {d k : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) {p : ℝ}
    (h : (transposeBob (hidingFamily p d k)).PosSemidef) : p ≤ 1 / 3 := by
  have := form_nonneg h (fun a => vp a.1 * φ1 a.2)
  rw [decompT', F_add, F_add, F_add, kron_form, kron_form, kron_form, kron_form, keyF.1, keyF.2.1,
    keyF.2.2.1, keyF.2.2.2.1] at this
  simp only [F_add, F_sub, F_smul, F_φ1] at this
  have e1 : tau (hidingOne d k) = 0 := by
    unfold hidingOne; rw [copies_tau, tau_base hd, zero_pow (by omega)]
  have e2 : tau (hidingTwo d k) = 1 := by
    unfold hidingTwo; rw [copies_tau, (sym_facts hd).2.2, one_pow]
  rw [e1, e2] at this
  have : (0 : ℂ) ≤ ((1 - 3 * p : ℝ) : ℂ) := by
    convert this using 1; push_cast; ring
  have := Complex.zero_le_real.mp this
  linarith

theorem entry_sym {d : ℕ} (hd : 2 ≤ d) (i j : Fin d) (hij : i ≠ j) :
    transposeSecond (symmetricWerner d) (i, j) (i, j) = (cs d : ℂ) := by
  rw [Γ_sym hd]
  simp [Qm, Pm_apply, hij]

theorem entry_base {d : ℕ} (hd : 2 ≤ d) (i j : Fin d) (hij : i ≠ j) :
    transposeSecond ((1 / 2 : ℂ) • (symmetricWerner d + antisymmetricWerner d)) (i, j) (i, j) =
      (x0 d : ℂ) := by
  rw [Γ_base hd]
  simp [Qm, Pm_apply, hij]

theorem cond2 {d k : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 0 < p)
    (h : (transposeBob (hidingFamily p d k)).PosSemidef) : ((d : ℝ) / (d - 1)) ^ k ≤ (1 - p) / p := by
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let z0 : (Fin k → Fin d) × (Fin k → Fin d) := (fun _ => i0, fun _ => i1)
  have := form_nonneg h (fun a => vm a.1 * (Pi.single z0 (1 : ℂ) : _ → ℂ) a.2)
  rw [decompT', F_add, F_add, F_add, kron_form, kron_form, kron_form, kron_form, keyF.2.2.2.2.1,
    keyF.2.2.2.2.2.1, keyF.2.2.2.2.2.2.1, keyF.2.2.2.2.2.2.2] at this
  simp only [F_add, F_sub, F_smul, F_single] at this
  have e1 : transposeSecond (hidingOne d k) z0 z0 = (x0 d : ℂ) ^ k := by
    have : transposeSecond (hidingOne d k) =
      bipartiteCopies (transposeSecond ((1 / 2 : ℂ) • (symmetricWerner d + antisymmetricWerner d))) k := rfl
    rw [this]
    simp only [bipartiteCopies, z0, entry_base hd i0 i1 hij, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have e2 : transposeSecond (hidingTwo d k) z0 z0 = (cs d : ℂ) ^ k := by
    have : transposeSecond (hidingTwo d k) =
      bipartiteCopies (transposeSecond (symmetricWerner d)) k := rfl
    rw [this]
    simp only [bipartiteCopies, z0, entry_sym hd i0 i1 hij, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [e1, e2] at this
  have : (0 : ℂ) ≤ (((1 - p) * cs d ^ k - p * x0 d ^ k : ℝ) : ℂ) := by
    convert this using 1; push_cast; ring
  have h0 := Complex.zero_le_real.mp this
  rw [ratio hd, mul_pow] at h0
  have hc : 0 < cs d ^ k := pow_pos (cs_pos hd) k
  rw [le_div_iff₀ hp]
  nlinarith

theorem density {d k : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 0 < p) (h2 : p ≤ 1 / 2) :
    IsDensityMatrix (hidingFamily p d k) := by
  have hb : ((1 / 2 : ℂ) • (symmetricWerner d + antisymmetricWerner d)).PosSemidef :=
    ((sym_facts hd).1.add (anti_facts hd).1).smul half_nonneg'
  have h1 : (hidingOne d k).PosSemidef := copies_psd _ hb k
  have h2' : (hidingTwo d k).PosSemidef := copies_psd _ (sym_facts hd).1 k
  have tr1 : (hidingOne d k).trace = 1 := by
    unfold hidingOne
    rw [copies_trace, Matrix.trace_smul, Matrix.trace_add, (sym_facts hd).2.1, (anti_facts hd).2.1]
    norm_num
  have tr2 : (hidingTwo d k).trace = 1 := by
    unfold hidingTwo; rw [copies_trace, (sym_facts hd).2.1, one_pow]
  refine ⟨?_, ?_⟩
  · rw [decomp]
    have c1 := cofp (by linarith : (0 : ℝ) ≤ p / 2)
    have c2 := cofp (by linarith : (0 : ℝ) ≤ 1 / 2 - p)
    exact (((KM_psd wp).kronecker (h1.smul c1)).add ((KM_psd wm).kronecker (h2'.smul c1))).add
      ((KM_psd e01).kronecker (h2'.smul c2)) |>.add ((KM_psd e10).kronecker (h2'.smul c2))
  · rw [decomp]
    have kt : ∀ c : Key 2 → ℂ, (KM c).trace = ∑ a, c a * star (c a) := fun c => by
      simp [KM, Matrix.trace, Matrix.vecMulVec_apply]
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, tk, tk, tk, tk]
    simp only [Matrix.trace_smul, tr1, tr2, smul_eq_mul, kt]
    simp [wp, wm, e01, e10, Fintype.sum_prod_type, Fin.sum_univ_two]
    push_cast; ring

theorem exists_d {k : ℕ} (hk : 1 ≤ k) {p : ℝ} (hp : 0 < p) (h3 : p ≤ 1 / 3) :
    ((((2 * k : ℕ) : ℝ)) / (((2 * k : ℕ) : ℝ) - 1)) ^ k ≤ (1 - p) / p := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set D : ℝ := ((2 * k : ℕ) : ℝ) with hD
  have hD2 : D = 2 * k := by rw [hD]; push_cast; ring
  have hDpos : 0 < D := by rw [hD2]; linarith
  have hbern := one_add_mul_le_pow (a := -(1 / D)) (by
    have : 1 / D ≤ 1 := by rw [div_le_one hDpos]; linarith
    linarith) k
  have hb : (1 : ℝ) / 2 ≤ ((D - 1) / D) ^ k := by
    have e : 1 + -(1 / D) = (D - 1) / D := by field_simp; ring
    rw [e] at hbern
    have : (k : ℝ) * -(1 / D) = -(1 / 2) := by rw [hD2]; field_simp
    linarith
  have hpos : 0 < ((D - 1) / D) ^ k := by linarith
  have e2 : (D / (D - 1)) ^ k = 1 / ((D - 1) / D) ^ k := by
    rw [← one_div_pow, one_div_div]
  rw [e2]
  have : 1 / ((D - 1) / D) ^ k ≤ 2 := by
    rw [div_le_iff₀ hpos]; linarith
  have : 2 ≤ (1 - p) / p := by rw [le_div_iff₀ hp]; linarith
  linarith

theorem main :
    (∀ d k : ℕ, 2 ≤ d → 1 ≤ k → ∀ p : ℝ, 0 < p → p ≤ 1/2 →
      IsDensityMatrix (hidingFamily p d k) ∧
      ((transposeBob (hidingFamily p d k)).PosSemidef ↔
        p ≤ 1/3 ∧ ((d:ℝ)/(d-1))^k ≤ (1-p)/p)) ∧
    (∀ p : ℝ, 0 < p → p ≤ 1/3 → ∀ k : ℕ, 1 ≤ k →
      ∃ d : ℕ, 2 ≤ d ∧ (transposeBob (hidingFamily p d k)).PosSemidef) := by
  refine ⟨fun d k hd hk p hp hp2 => ⟨density hd hp hp2, fun h => ⟨cond1 hd hk h, cond2 hd hp h⟩,
    fun h => ppt_of hd hp h.1 h.2⟩, fun p hp h3 k hk => ⟨2 * k, by omega, ?_⟩⟩
  exact ppt_of (by omega) hp h3 (exists_d hk hp h3)

end A3HP

end QAlgorithms.Papers.Independent.Dependency50.P24

end

open scoped Matrix ComplexOrder in
open QAlgorithms.Papers.Independent.Dependency50.P24 in
theorem solution :
    (∀ d k : ℕ, 2 ≤ d → 1 ≤ k → ∀ p : ℝ, 0 < p → p ≤ 1/2 →
      QAlgorithms.IsDensityMatrix (hidingFamily p d k) ∧
      ((transposeBob (hidingFamily p d k)).PosSemidef ↔
        p ≤ 1/3 ∧ ((d:ℝ)/(d-1))^k ≤ (1-p)/p)) ∧
    (∀ p : ℝ, 0 < p → p ≤ 1/3 → ∀ k : ℕ, 1 ≤ k →
      ∃ d : ℕ, 2 ≤ d ∧ (transposeBob (hidingFamily p d k)).PosSemidef) :=
  QAlgorithms.Papers.Independent.Dependency50.P24.A3HP.main

#print axioms solution
