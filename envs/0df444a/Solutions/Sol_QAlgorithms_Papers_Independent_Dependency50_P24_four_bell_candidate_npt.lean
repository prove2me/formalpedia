-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.four_bell_candidate_npt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:29:40.438536+00:00
-- url     : https://prove2.me/submissions/1870eef0-5d7c-4de3-85b8-c8c7f0c1a77f

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

namespace A3FB

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

theorem main (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) :
    IsDensityMatrix (nptCandidate d k) ∧ ¬ (transposeBob (nptCandidate d k)).PosSemidef := by
  obtain ⟨sP, sT, sτ⟩ := sym_facts hd
  obtain ⟨aP, aT, aτ⟩ := anti_facts hd
  set base : Op (Fin d × Fin d) := (1 / 2 : ℂ) • (symmetricWerner d + antisymmetricWerner d)
    with hbase
  have bP : base.PosSemidef := (sP.add aP).smul half_nonneg'
  have bT : base.trace = 1 := by
    rw [hbase, Matrix.trace_smul, Matrix.trace_add, sT, aT]; norm_num
  have bτ : tau base = 0 := by
    rw [hbase, tau_smul, tau_add, sτ, aτ]; norm_num
  have h1P : (hidingOne d k).PosSemidef := copies_psd _ bP k
  have h2P : (hidingTwo d k).PosSemidef := copies_psd _ sP k
  have h1T : (hidingOne d k).trace = 1 := by
    unfold hidingOne; rw [copies_trace, ← hbase, bT, one_pow]
  have h2T : (hidingTwo d k).trace = 1 := by
    unfold hidingTwo; rw [copies_trace, sT, one_pow]
  have h1τ : tau (hidingOne d k) = 0 := by
    unfold hidingOne; rw [copies_tau, ← hbase, bτ, zero_pow (by omega)]
  have h2τ : tau (hidingTwo d k) = 1 := by
    unfold hidingTwo; rw [copies_tau, sτ, one_pow]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold nptCandidate
    refine Matrix.PosSemidef.smul ?_ quarter_nonneg'
    refine (((?_ : Matrix.PosSemidef _).add ?_).add ?_).add ?_ <;>
      exact (bell_psd _ _).kronecker (paired_psd _ _ (by assumption) (by assumption))
  · unfold nptCandidate
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, tk, tk, tk, tk]
    simp only [paired_trace, bell_trace, h1T, h2T]
    norm_num
  · intro h
    have hnn := h.dotProduct_mulVec_nonneg wit
    rw [witness] at hnn
    have hQ : Q (nptCandidate d k) = -1 / 4 := by
      unfold nptCandidate
      rw [Q_smul, Q_add, Q_add, Q_add, Q_kron, Q_kron, Q_kron, Q_kron, bsum_ff, bsum_ft, bsum_tf, bsum_tt, h1τ, h2τ]
      norm_num
    rw [hQ] at hnn
    have := (Complex.nonneg_iff.mp hnn).1
    norm_num at this

end A3FB

end QAlgorithms.Papers.Independent.Dependency50.P24

end

open scoped ComplexOrder in
theorem solution (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) :
    QAlgorithms.IsDensityMatrix (QAlgorithms.Papers.Independent.Dependency50.P24.nptCandidate d k) ∧
      ¬ (QAlgorithms.Papers.Independent.Dependency50.P24.transposeBob
        (QAlgorithms.Papers.Independent.Dependency50.P24.nptCandidate d k)).PosSemidef :=
  QAlgorithms.Papers.Independent.Dependency50.P24.A3FB.main d k hd hk
