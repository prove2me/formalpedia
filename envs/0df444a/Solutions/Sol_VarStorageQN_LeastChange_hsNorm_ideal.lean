-- Prove2me | solution 1 for VarStorageQN.LeastChange.hsNorm_ideal
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:40:46.112377+00:00
-- url     : https://prove2.me/submissions/d35a6fac-6209-4af2-a912-3b94edaac2e7

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
import Definitions.Def_VarStorageQN_LeastChange_Bracket

set_option autoImplicit false
open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace
open VarStorageQN.LeastChange

namespace VSQhelp
open VarStorageQN.LeastChange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem parseval {ι : Type*} (b : HilbertBasis ι ℝ H) (x : H) :
    HasSum (fun i => ⟪x, b i⟫_ℝ ^ 2) (‖x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at h
  have e : (fun i => ⟪x, b i⟫_ℝ ^ 2) = fun i => ⟪x, b i⟫_ℝ * ⟪b i, x⟫_ℝ := by
    funext i
    rw [real_inner_comm (b i) x, sq]
  rw [e]; exact h

theorem hasSum_bracket {ι : Type*} (b : HilbertBasis ι ℝ H) (u v : H) :
    HasSum (fun i => ‖bracket u v (b i)‖ ^ 2) (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  have h := (parseval b v).mul_left (‖u‖ ^ 2)
  have e : (fun i => ‖bracket u v (b i)‖ ^ 2) = fun i => ‖u‖ ^ 2 * ⟪v, b i⟫_ℝ ^ 2 := by
    funext i
    rw [bracket, rankOne_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [e]; exact h

theorem hsSummable_bracket {ι : Type*} (b : HilbertBasis ι ℝ H) (u v : H) :
    HSSummable b (bracket u v) := (hasSum_bracket b u v).summable

theorem hsNorm_bracket {ι : Type*} (b : HilbertBasis ι ℝ H) (u v : H) :
    hsNorm b (bracket u v) = ‖u‖ * ‖v‖ := by
  unfold hsNorm
  rw [(hasSum_bracket b u v).tsum_eq, ← mul_pow]
  exact Real.sqrt_sq (by positivity)

end VSQhelp
namespace VSQhelp
open VarStorageQN.LeastChange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- ENNReal version of the Hilbert–Schmidt sum. -/
noncomputable def E {ι : Type*} (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) : ENNReal :=
  ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)

theorem ofReal_sq_norm_eq {κ : Type*} (f : HilbertBasis κ ℝ H) (x : H) :
    ENNReal.ofReal (‖x‖ ^ 2) = ∑' j, ENNReal.ofReal (⟪x, f j⟫_ℝ ^ 2) := by
  rw [← (parseval f x).tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) (parseval f x).summable]

theorem E_adjoint {ι κ : Type*} (b : HilbertBasis ι ℝ H) (f : HilbertBasis κ ℝ H) (A : H →L[ℝ] H) :
    E b A = E f (adjoint A) := by
  unfold E
  have h1 : ∀ i, ENNReal.ofReal (‖A (b i)‖ ^ 2) = ∑' j, ENNReal.ofReal (⟪A.adjoint (f j), b i⟫_ℝ ^ 2) := by
    intro i
    rw [ofReal_sq_norm_eq f]
    refine tsum_congr fun j => ?_
    rw [adjoint_inner_left, real_inner_comm]
  have h2 : ∀ j, ENNReal.ofReal (‖A.adjoint (f j)‖ ^ 2) = ∑' i, ENNReal.ofReal (⟪A.adjoint (f j), b i⟫_ℝ ^ 2) := by
    intro j
    rw [ofReal_sq_norm_eq b]
  simp_rw [h1, h2]
  exact ENNReal.tsum_comm

theorem hsSummable_iff_E {ι : Type*} (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    HSSummable b A ↔ E b A ≠ ⊤ := by
  unfold HSSummable E
  constructor
  · intro h
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h]
    exact ENNReal.ofReal_ne_top
  · intro h
    have := ENNReal.summable_toReal h
    simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using this

theorem E_eq_ofReal {ι : Type*} (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (h : HSSummable b A) :
    E b A = ENNReal.ofReal (∑' i, ‖A (b i)‖ ^ 2) := by
  unfold E
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h]

theorem tsum_adjoint {ι κ : Type*} (b : HilbertBasis ι ℝ H) (f : HilbertBasis κ ℝ H) (A : H →L[ℝ] H)
    (h : HSSummable b A) :
    HSSummable f (adjoint A) ∧ ∑' i, ‖A (b i)‖ ^ 2 = ∑' j, ‖adjoint A (f j)‖ ^ 2 := by
  have hE := E_adjoint b f A
  have h1 : HSSummable f (adjoint A) := by
    rw [hsSummable_iff_E, ← hE]; exact (hsSummable_iff_E b A).mp h
  refine ⟨h1, ?_⟩
  rw [E_eq_ofReal b A h, E_eq_ofReal f _ h1] at hE
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun _ => sq_nonneg _) (tsum_nonneg fun _ => sq_nonneg _)).mp hE

theorem hs_adjoint_iff {ι κ : Type*} (b : HilbertBasis ι ℝ H) (f : HilbertBasis κ ℝ H) (A : H →L[ℝ] H) :
    HSSummable b A ↔ HSSummable f (adjoint A) := by
  rw [hsSummable_iff_E, hsSummable_iff_E, E_adjoint b f A]

theorem hs_basis_iff {ι κ : Type*} (b : HilbertBasis ι ℝ H) (f : HilbertBasis κ ℝ H) (A : H →L[ℝ] H) :
    HSSummable b A ↔ HSSummable f A := by
  rw [hs_adjoint_iff b f A, hs_adjoint_iff f f (adjoint A), adjoint_adjoint]


theorem tsum_basis {ι κ : Type*} (b : HilbertBasis ι ℝ H) (f : HilbertBasis κ ℝ H) (A : H →L[ℝ] H)
    (h : HSSummable b A) :
    ∑' i, ‖A (b i)‖ ^ 2 = ∑' j, ‖A (f j)‖ ^ 2 := by
  obtain ⟨h1, e1⟩ := tsum_adjoint b b A h
  obtain ⟨h2, e2⟩ := tsum_adjoint b f (adjoint A) h1
  rw [adjoint_adjoint] at e2
  rw [e1, e2]

theorem hsNorm_basis {ι κ : Type*} (b : HilbertBasis ι ℝ H) (f : HilbertBasis κ ℝ H) (A : H →L[ℝ] H)
    (h : HSSummable b A) : hsNorm b A = hsNorm f A := by
  unfold hsNorm
  rw [tsum_basis b f A h]

end VSQhelp
namespace VSQhelp
open VarStorageQN.LeastChange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem hsNorm_sq {ι : Type*} (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    hsNorm b A ^ 2 = ∑' i, ‖A (b i)‖ ^ 2 := by
  unfold hsNorm
  exact Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)

theorem hsNorm_nonneg {ι : Type*} (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) : 0 ≤ hsNorm b A :=
  Real.sqrt_nonneg _

theorem memℓp_of_hs {ι : Type*} (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (h : HSSummable b A) :
    Memℓp (fun i => A (b i)) 2 := by
  rw [memℓp_gen_iff (by simp)]
  have h' : Summable fun i => ‖A (b i)‖ ^ 2 := h
  simpa using h'

noncomputable def toLp {ι : Type*} (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (h : HSSummable b A) :
    lp (fun _ : ι => H) 2 := ⟨fun i => A (b i), memℓp_of_hs b A h⟩

theorem norm_toLp {ι : Type*} (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (h : HSSummable b A) :
    ‖toLp b A h‖ = hsNorm b A := by
  rw [lp.norm_eq_tsum_rpow (by simp)]
  unfold hsNorm toLp
  rw [Real.sqrt_eq_rpow]
  simp [Real.rpow_two]

theorem hs_add {ι : Type*} (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) (hA : HSSummable b A)
    (hB : HSSummable b B) : HSSummable b (A + B) ∧ hsNorm b (A + B) ≤ hsNorm b A + hsNorm b B := by
  have hm : Memℓp (fun i => (A + B) (b i)) 2 := by
    have := (memℓp_of_hs b A hA).add (memℓp_of_hs b B hB)
    have e : (fun i => (A + B) (b i)) = (fun i => A (b i)) + (fun i => B (b i)) := by
      funext i; simp
    rw [e]; exact this
  have hAB : HSSummable b (A + B) := by
    have := (memℓp_gen_iff (p := (2 : ENNReal)) (E := fun _ : ι => H) (by simp)).mp hm
    show Summable fun i => ‖(A + B) (b i)‖ ^ 2
    simpa using this
  refine ⟨hAB, ?_⟩
  have e : toLp b (A + B) hAB = toLp b A hA + toLp b B hB := by
    apply lp.ext
    funext i
    simp [toLp]
    rfl
  rw [← norm_toLp b _ hAB, ← norm_toLp b _ hA, ← norm_toLp b _ hB, e]
  exact norm_add_le _ _

theorem hs_smul {ι : Type*} (b : HilbertBasis ι ℝ H) (c : ℝ) (A : H →L[ℝ] H) (hA : HSSummable b A) :
    HSSummable b (c • A) ∧ hsNorm b (c • A) = |c| * hsNorm b A := by
  have h1 : HSSummable b (c • A) := by
    unfold HSSummable at *
    have := hA.mul_left (c ^ 2)
    refine this.congr fun i => ?_
    simp [norm_smul, mul_pow]
  refine ⟨h1, ?_⟩
  unfold hsNorm
  have : ∑' i, ‖(c • A) (b i)‖ ^ 2 = c ^ 2 * ∑' i, ‖A (b i)‖ ^ 2 := by
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    simp [norm_smul, mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem hs_zero_iff {ι : Type*} (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (h : HSSummable b A) :
    hsNorm b A = 0 ↔ A = 0 := by
  constructor
  · intro h0
    have h2 : ∑' i, ‖A (b i)‖ ^ 2 = 0 := by rw [← hsNorm_sq, h0]; norm_num
    have h3 : HasSum (fun i => ‖A (b i)‖ ^ 2) 0 := h2 ▸ h.hasSum
    have h4 := (hasSum_zero_iff_of_nonneg (fun i => sq_nonneg ‖A (b i)‖)).mp h3
    refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) (s := Set.range b) ?_
    rintro _ ⟨i, rfl⟩
    have := congrFun h4 i
    simpa using this
  · rintro rfl
    simp [hsNorm]

theorem hs_zero {ι : Type*} (b : HilbertBasis ι ℝ H) : HSSummable b (0 : H →L[ℝ] H) := by
  simp [HSSummable, summable_zero]

end VSQhelp
namespace VSQhelp
open VarStorageQN.LeastChange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem opNorm_le_hs {ι : Type*} (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (h : HSSummable b A) :
    ‖A‖ ≤ hsNorm b A := by
  obtain ⟨h1, e1⟩ := tsum_adjoint b b A h
  refine ContinuousLinearMap.opNorm_le_bound _ (hsNorm_nonneg b A) fun x => ?_
  have hp := parseval b (A x)
  have hs : Summable fun j => ‖x‖ ^ 2 * ‖adjoint A (b j)‖ ^ 2 := h1.mul_left _
  have hle : ∀ j, ⟪A x, b j⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * ‖adjoint A (b j)‖ ^ 2 := by
    intro j
    rw [← adjoint_inner_right, ← mul_pow]
    have := abs_real_inner_le_norm x (adjoint A (b j))
    exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
  have hsum := hasSum_le hle hp hs.hasSum
  rw [tsum_mul_left, ← e1, ← hsNorm_sq] at hsum
  have h0 : 0 ≤ hsNorm b A * ‖x‖ := mul_nonneg (hsNorm_nonneg b A) (norm_nonneg x)
  by_contra hcon
  push_neg at hcon
  nlinarith [norm_nonneg (A x)]

theorem hs_comp_right {ι : Type*} (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) (hB : HSSummable b B) :
    HSSummable b (A ∘L B) := by
  have h1 : Summable fun i => ‖A‖ ^ 2 * ‖B (b i)‖ ^ 2 := hB.mul_left _
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) h1
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2

theorem hs_comp_left {ι : Type*} (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) (hA : HSSummable b A) :
    HSSummable b (A ∘L B) := by
  rw [hs_adjoint_iff b b, adjoint_comp]
  exact hs_comp_right b _ _ ((hs_adjoint_iff b b A).mp hA)

end VSQhelp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem solution {ι : Type*} (b : HilbertBasis ι ℝ H) :
    (∀ A : H →L[ℝ] H, HSSummable b A → ‖A‖ ≤ hsNorm b A) ∧
    (∀ A B : H →L[ℝ] H,
      (HSSummable b A ∨ HSSummable b B) → HSSummable b (A ∘L B)) := by
  refine ⟨fun A hA => VSQhelp.opNorm_le_hs b A hA, fun A B h => ?_⟩
  rcases h with h | h
  · exact VSQhelp.hs_comp_left b A B h
  · exact VSQhelp.hs_comp_right b A B h
