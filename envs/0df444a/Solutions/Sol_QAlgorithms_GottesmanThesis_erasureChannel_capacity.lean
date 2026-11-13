-- Prove2me | solution 1 for QAlgorithms.GottesmanThesis.erasureChannel_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T14:52:24.545967+00:00
-- url     : https://prove2.me/submissions/f5aa12f6-e093-4ca8-9daf-706e846d52f7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Theorems.Thm_QAlgorithms_GottesmanThesis_erasure_achievable_one_sub_two_mul
import Theorems.Thm_QAlgorithms_GottesmanThesis_erasure_not_achievable_of_half_le
import Theorems.Thm_QAlgorithms_GottesmanThesis_erasure_rate_le_one_sub_two_mul
set_option autoImplicit false

namespace EC74504552

open QAlgorithms
open scoped ComplexConjugate Matrix

/-- Any finite normalized Kraus family (any index type) gives a channel. -/
theorem isChannel_of_kraus {K ι κ : Type*} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : IsKrausFamily E) : IsChannel (krausApply E) := by
  classical
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun i => E (e.symm i), ?_, fun ρ => ?_⟩
  · unfold IsKrausFamily at *
    rw [← hE]
    exact Equiv.sum_comp e.symm (fun j => (E j)ᴴ * E j)
  · unfold krausApply
    exact (Equiv.sum_comp e.symm (fun j => E j * ρ * (E j)ᴴ)).symm

/-- A normalized Kraus map preserves the trace. -/
theorem trace_krausApply {K ι κ : Type*} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : IsKrausFamily E) (M : Matrix ι ι ℂ) :
    (krausApply E M).trace = M.trace := by
  unfold krausApply
  rw [Matrix.trace_sum]
  have : ∀ j, (E j * M * (E j)ᴴ).trace = ((E j)ᴴ * E j * M).trace := by
    intro j
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  unfold IsKrausFamily at hE
  rw [hE, Matrix.one_mul]

/-- Tensor powers of a normalized Kraus family are normalized. -/
theorem prodKraus_isKraus {n : ℕ} {K α β : Type*} [Fintype K] [Fintype α] [Fintype β]
    [DecidableEq β] (E : K → Matrix α β ℂ) (hE : IsKrausFamily E) :
    IsKrausFamily (fun j : Fin n → K =>
      (Matrix.of fun (y : Fin n → α) (z : Fin n → β) => ∏ q, E (j q) (y q) (z q))) := by
  classical
  unfold IsKrausFamily at *
  have h1 : ∀ a b : β, ∑ k, ∑ x, star (E k x a) * E k x b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hE a) b
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply] using this
  ext z z'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  have h2 : ∀ (j : Fin n → K) (y : Fin n → α),
      star (∏ q, E (j q) (y q) (z q)) * ∏ q, E (j q) (y q) (z' q)
        = ∏ q, (star (E (j q) (y q) (z q)) * E (j q) (y q) (z' q)) := by
    intro j y
    rw [star_prod, ← Finset.prod_mul_distrib]
  simp_rw [h2]
  have h3 : ∀ j : Fin n → K, ∑ y : Fin n → α, ∏ q, (star (E (j q) (y q) (z q)) * E (j q) (y q) (z' q))
      = ∏ q, ∑ x, (star (E (j q) x (z q)) * E (j q) x (z' q)) := by
    intro j
    rw [Fintype.prod_sum]
  simp_rw [h3]
  rw [← Fintype.prod_sum (fun q k => ∑ x, (star (E k x (z q)) * E k x (z' q)))]
  simp_rw [h1]
  rw [Finset.prod_boole]
  by_cases h : z = z'
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hall
    exact h (funext fun q => hall q (Finset.mem_univ q))

theorem erasure_isKraus (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsKrausFamily (fun j : Fin n → Fin 5 =>
      (Matrix.of fun (y : Fin n → Bool × Bool) (z : Qubits n) => ∏ q, erasureKraus p (j q) (y q) (z q))) :=
  prodKraus_isKraus (erasureKraus p) (erasureKraus_isKraus hp0 hp1)

theorem erasureChannel_isChannel (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsChannel (erasureChannel n p) :=
  isChannel_of_kraus _ (erasure_isKraus n p hp0 hp1)

theorem trace_erasureChannel (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (M : Matrix (Qubits n) (Qubits n) ℂ) : (erasureChannel n p M).trace = M.trace :=
  trace_krausApply _ (erasure_isKraus n p hp0 hp1) M

/-- Achievable rates are downward closed. -/
theorem achievable_mono {Out : ℕ → Type*} [∀ n, Fintype (Out n)] [∀ n, DecidableEq (Out n)]
    (Nch : (n : ℕ) → Superop (Qubits n) (Out n)) {R R' : ℝ} (h : IsAchievableQRate Nch R)
    (hR : R' ≤ R) : IsAchievableQRate Nch R' := by
  intro ε hε δ hδ
  obtain ⟨N₀, hN⟩ := h ε hε δ hδ
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨k, hk, rest⟩ := hN n hn
  refine ⟨k, le_trans ?_ hk, rest⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)

/-- On zero qubits the entanglement fidelity of a map fixing the single entry is `1`. -/
theorem fid_zero (Φ : Superop (Qubits 0) (Qubits 0))
    (hΦ : ∀ M : Matrix (Qubits 0) (Qubits 0) ℂ, Φ M default default = M default default) :
    entanglementFidelity Φ = 1 := by
  unfold entanglementFidelity idTensorSuperop
  have hd : ∀ x : Qubits 0 × Qubits 0, x = (default, default) := fun x => Subsingleton.elim _ _
  rw [Fintype.sum_eq_single (default, default) (fun a ha => absurd (hd a) ha)]
  rw [Fintype.sum_eq_single (default, default) (fun a ha => absurd (hd a) ha)]
  simp only [Matrix.of_apply, hΦ]
  simp [maxEntangled, pureDensity]

theorem achievable_of_nonpos (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (R : ℝ) (hR : R ≤ 0) :
    IsAchievableQRate (fun n => erasureChannel n p) R := by
  classical
  intro ε hε δ hδ
  refine ⟨0, fun n _ => ⟨0, ?_, ?_⟩⟩
  · have : (R - δ) * (n : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg n)
    simpa using this
  · let v : Matrix (Qubits n) (Qubits 0) ℂ :=
      Matrix.of fun y _ => if y = (fun _ => false) then 1 else 0
    let w : (Fin n → Bool × Bool) → Matrix (Qubits 0) (Fin n → Bool × Bool) ℂ :=
      fun y => Matrix.of fun _ y' => if y' = y then 1 else 0
    have hv : IsKrausFamily (fun _ : Fin 1 => v) := by
      unfold IsKrausFamily
      ext a b
      have ha : a = b := Subsingleton.elim _ _
      subst ha
      simp [v, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hw : IsKrausFamily w := by
      unfold IsKrausFamily
      ext a b
      simp [w, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    refine ⟨krausApply (fun _ : Fin 1 => v), isChannel_of_kraus _ hv, krausApply w,
      isChannel_of_kraus _ hw, ?_⟩
    have hfid : entanglementFidelity
        (krausApply w ∘ (fun n => erasureChannel n p) n ∘ krausApply (fun _ : Fin 1 => v)) = 1 := by
      apply fid_zero
      intro M
      have htr : ∀ X : Matrix (Qubits 0) (Qubits 0) ℂ, X default default = X.trace := by
        intro X; rw [Matrix.trace, Fintype.sum_unique, Matrix.diag_apply]
        exact congr (congrArg X (Subsingleton.elim _ _)) (Subsingleton.elim _ _)
      simp only [Function.comp_apply]
      calc _ = (krausApply w (erasureChannel n p (krausApply (fun _ : Fin 1 => v) M))).trace :=
            htr _
        _ = M.trace := by
            rw [trace_krausApply _ hw, trace_erasureChannel n p hp0 hp1, trace_krausApply _ hv]
        _ = M default default := (htr M).symm
    rw [hfid]; linarith

/-- The reduction core: the parent from its three children
(achievability at `1 − 2p`, the no-cloning bound for `p ≥ 1/2`, the converse for `p < 1/2`). -/
theorem parent_of_children
    (hach : ∀ p : ℝ, 0 ≤ p → p < 1 / 2 →
      IsAchievableQRate (fun n => erasureChannel n p) (1 - 2 * p))
    (hcl : ∀ p : ℝ, 1 / 2 ≤ p → p ≤ 1 → ∀ R : ℝ, 0 < R →
      ¬ IsAchievableQRate (fun n => erasureChannel n p) R)
    (hconv : ∀ p : ℝ, 0 ≤ p → p < 1 / 2 → ∀ R : ℝ,
      IsAchievableQRate (fun n => erasureChannel n p) R → R ≤ 1 - 2 * p)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (R : ℝ) :
    IsAchievableQRate (fun n => erasureChannel n p) R ↔ R ≤ max 0 (1 - 2 * p) := by
  constructor
  · intro h
    by_cases hp : p < 1 / 2
    · exact le_trans (hconv p hp0 hp R h) (le_max_right _ _)
    · by_contra hc
      push Not at hc
      exact hcl p (by linarith) hp1 R (lt_of_le_of_lt (le_max_left _ _) hc) h
  · intro hR
    by_cases h0 : R ≤ 0
    · exact achievable_of_nonpos p hp0 hp1 R h0
    · push Not at h0
      have h1 : R ≤ 1 - 2 * p := by
        rcases le_max_iff.mp hR with h | h
        · linarith
        · exact h
      exact achievable_mono _ (hach p hp0 (by linarith) ) h1

end EC74504552

open QAlgorithms in
theorem solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (R : ℝ) :
    IsAchievableQRate (fun n => erasureChannel n p) R ↔ R ≤ max 0 (1 - 2 * p) := by
  exact EC74504552.parent_of_children
    (fun p hp0 hp => QAlgorithms.GottesmanThesis.erasure_achievable_one_sub_two_mul p hp0 hp)
    (fun p hp hp1 R hR => QAlgorithms.GottesmanThesis.erasure_not_achievable_of_half_le p hp hp1 R hR)
    (fun p hp0 hp R h => QAlgorithms.GottesmanThesis.erasure_rate_le_one_sub_two_mul p hp0 hp R h)
    p hp0 hp1 R
