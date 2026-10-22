-- Prove2me | solution 1 for VarStorageQN.LeastChange.dfp_update
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T17:29:13.845389+00:00
-- url     : https://prove2.me/submissions/5aa7177e-b724-4ec7-817d-bcc87afebedc

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
import Definitions.Def_VarStorageQN_LeastChange_Bracket
import Definitions.Def_VarStorageQN_LeastChange_SecantProblem

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

theorem hasSum_inner_bracket {ι : Type*} (b : HilbertBasis ι ℝ H) (D : H →L[ℝ] H) (u v : H) :
    HasSum (fun i => ⟪bracket u v (b i), D (b i)⟫_ℝ) ⟪D v, u⟫_ℝ := by
  have h := b.hasSum_inner_mul_inner v (adjoint D u)
  rw [adjoint_inner_right] at h
  have e : (fun i => ⟪bracket u v (b i), D (b i)⟫_ℝ) = fun i => ⟪v, b i⟫_ℝ * ⟪b i, adjoint D u⟫_ℝ := by
    funext i
    rw [bracket, rankOne_apply, inner_smul_left, ← adjoint_inner_left, real_inner_comm (b i)
      (adjoint D u)]
    simp
  rw [e]
  exact h

theorem pyth {ι : Type*} (b : HilbertBasis ι ℝ H) (A D : H →L[ℝ] H) (hA : HSSummable b A)
    (hD : HSSummable b D) (κ : ℝ) (hc : HasSum (fun i => ⟪A (b i), D (b i)⟫_ℝ) κ) :
    hsNorm b (A + D) ^ 2 = hsNorm b A ^ 2 + 2 * κ + hsNorm b D ^ 2 := by
  have h := hA.hasSum.add ((hc.mul_left 2).add hD.hasSum)
  have e : (fun i => ‖A (b i)‖ ^ 2 + (2 * ⟪A (b i), D (b i)⟫_ℝ + ‖D (b i)‖ ^ 2)) =
      fun i => ‖(A + D) (b i)‖ ^ 2 := by
    funext i
    rw [add_apply, norm_add_sq_real]; ring
  rw [e] at h
  rw [hsNorm_sq, hsNorm_sq, hsNorm_sq, h.tsum_eq, hA.hasSum.tsum_eq, hD.hasSum.tsum_eq]
  ring

theorem comp_bracket (R : H →L[ℝ] H) (u v : H) : R ∘L bracket u v = bracket (R u) v := by
  ext d
  simp [bracket, rankOne_apply]

theorem bracket_comp (R : H →L[ℝ] H) (u v : H) : bracket u v ∘L R = bracket u (adjoint R v) := by
  ext d
  simp [bracket, rankOne_apply, adjoint_inner_left]

end VSQhelp
namespace VSQhelp
open VarStorageQN.LeastChange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem hs_sub {ι : Type*} (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) (hA : HSSummable b A)
    (hB : HSSummable b B) : HSSummable b (A - B) := by
  have := (hs_add b A ((-1 : ℝ) • B) hA (hs_smul b (-1) B hB).1).1
  simpa [sub_eq_add_neg] using this

theorem psb_core {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H) (y s : H) (hs : s ≠ 0) :
    let r := y - B s
    let Pc : H →L[ℝ] H :=
      (‖s‖ ^ 2)⁻¹ • (bracket r s + bracket s r) - (⟪r, s⟫_ℝ / ‖s‖ ^ 4) • bracket s s
    let obj : (H →L[ℝ] H) → ℝ := fun P => hsNorm b P
    Pc ∈ FeasSym b B y s ∧
      (∀ P ∈ FeasSym b B y s, obj Pc ≤ obj P) ∧
      (∀ P ∈ FeasSym b B y s, (∀ Q ∈ FeasSym b B y s, obj P ≤ obj Q) → P = Pc) := by
  intro r Pc obj
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hn2 : ‖s‖ ^ 2 ≠ 0 := by positivity
  have hn4 : ‖s‖ ^ 4 ≠ 0 := by positivity
  have hn' : ‖s‖ ≠ 0 := hn.ne'
  set t : ℝ := (‖s‖ ^ 2)⁻¹ with ht
  set u : ℝ := ⟪r, s⟫_ℝ / ‖s‖ ^ 4 with hu
  have hss : ⟪s, s⟫_ℝ = ‖s‖ ^ 2 := real_inner_self_eq_norm_sq s
  have hPcs : Pc s = r := by
    show (t • (bracket r s + bracket s r) - u • bracket s s) s = r
    simp only [sub_apply, smul_apply, add_apply, bracket, rankOne_apply, hss]
    rw [ht, hu]
    match_scalars <;> field_simp <;> ring
  have hPcHS : HSSummable b Pc := by
    refine hs_sub b _ _ (hs_smul b t _ (hs_add b _ _ (hsSummable_bracket b _ _)
      (hsSummable_bracket b _ _)).1).1 (hs_smul b u _ (hsSummable_bracket b _ _)).1
  have hPcSA : IsSelfAdjoint Pc := by
    have h1 : IsSelfAdjoint (bracket r s + bracket s r) := by
      show star _ = _
      rw [star_add, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
        bracket, bracket, adjoint_rankOne, adjoint_rankOne, add_comm]
    have h2 : IsSelfAdjoint (bracket s s) := by
      show star _ = _
      rw [ContinuousLinearMap.star_eq_adjoint, bracket, adjoint_rankOne]
    exact ((IsSelfAdjoint.all t).smul h1).sub ((IsSelfAdjoint.all u).smul h2)
  have hPcF : Pc ∈ FeasSym b B y s := by
    refine ⟨hPcHS, hPcSA, ?_⟩
    show (B + Pc) s = y
    rw [add_apply, hPcs]; simp [r]
  have key : ∀ P ∈ FeasSym b B y s, ∃ D : H →L[ℝ] H, HSSummable b D ∧ P = Pc + D ∧
      obj P ^ 2 = obj Pc ^ 2 + hsNorm b D ^ 2 := by
    intro P hP
    obtain ⟨hP1, hP2, hP3⟩ := hP
    have hPs : P s = r := by
      have : B s + P s = y := by simpa using hP3
      exact eq_sub_of_add_eq' this
    set D : H →L[ℝ] H := P - Pc with hD
    have hDHS : HSSummable b D := hs_sub b _ _ hP1 hPcHS
    have hDSA : IsSelfAdjoint D := hP2.sub hPcSA
    have hsplit : P = Pc + D := by rw [hD]; abel
    have hDs : D s = 0 := by rw [hD, sub_apply, hPs, hPcs, sub_self]
    have hsym : ∀ x z : H, ⟪D x, z⟫_ℝ = ⟪x, D z⟫_ℝ :=
      fun x z => (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hDSA) x z
    have hDrs : ⟪D r, s⟫_ℝ = 0 := by rw [hsym, hDs, inner_zero_right]
    have hcross : HasSum (fun i => ⟪Pc (b i), D (b i)⟫_ℝ) 0 := by
      have h1 := hasSum_inner_bracket b D r s
      have h2 := hasSum_inner_bracket b D s r
      have h3 := hasSum_inner_bracket b D s s
      have h4 := ((h1.add h2).mul_left t).sub (h3.mul_left u)
      rw [hDs, hDrs] at h4
      simp only [inner_zero_left, add_zero, mul_zero, sub_zero] at h4
      have e : (fun i => ⟪Pc (b i), D (b i)⟫_ℝ) =
          fun i => t * (⟪bracket r s (b i), D (b i)⟫_ℝ + ⟪bracket s r (b i), D (b i)⟫_ℝ) -
            u * ⟪bracket s s (b i), D (b i)⟫_ℝ := by
        funext i
        simp only [Pc, sub_apply, smul_apply, add_apply, inner_sub_left, inner_smul_left,
          inner_add_left, RCLike.conj_to_real]
        rfl
      rw [e]; exact h4
    have hp := pyth b Pc D hPcHS hDHS 0 hcross
    refine ⟨D, hDHS, hsplit, ?_⟩
    show hsNorm b P ^ 2 = hsNorm b Pc ^ 2 + _
    rw [hsplit, hp]; ring
  refine ⟨hPcF, ?_, ?_⟩
  · intro P hP
    obtain ⟨D, hD1, -, hD3⟩ := key P hP
    have h0 : 0 ≤ obj P := hsNorm_nonneg b _
    have h1 : 0 ≤ obj Pc := hsNorm_nonneg b _
    by_contra hcon
    push_neg at hcon
    have := sq_nonneg (hsNorm b D)
    nlinarith
  · intro P hP hmin
    obtain ⟨D, hD1, hD2, hD3⟩ := key P hP
    have hle := hmin Pc hPcF
    have h0 : 0 ≤ obj P := hsNorm_nonneg b _
    have h1 : 0 ≤ obj Pc := hsNorm_nonneg b _
    have hD0 : hsNorm b D = 0 := by
      have : hsNorm b D ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
    have hD00 : D = 0 := (hs_zero_iff b D hD1).mp hD0
    rw [hD00, add_zero] at hD2
    exact hD2

end VSQhelp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem accepted_psb {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H)
    (hB : IsSelfAdjoint B) (y s : H) (hs : s ≠ 0) :
    let r := y - B s
    let Pc : H →L[ℝ] H :=
      (‖s‖ ^ 2)⁻¹ • (bracket r s + bracket s r) - (⟪r, s⟫_ℝ / ‖s‖ ^ 4) • bracket s s
    let obj : (H →L[ℝ] H) → ℝ := fun P => hsNorm b P
    Pc ∈ FeasSym b B y s ∧
      (∀ P ∈ FeasSym b B y s, obj Pc ≤ obj P) ∧
      (∀ P ∈ FeasSym b B y s, (∀ Q ∈ FeasSym b B y s, obj P ≤ obj Q) → P = Pc) :=
  VSQhelp.psb_core b B y s hs

/- The two ideal-property lemmas below retain vebis's accepted proof bodies
   (submission d35a6fac-6209-4af2-a912-3b94edaac2e7). The preceding full PSB
   implementation is vebis's accepted source, with only solution renamed.
   The weighted congruence reduction below is the current contribution. -/
namespace VSQhelp
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

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

open VSQhelp

theorem accepted_weighted {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H)
    (hB : IsSelfAdjoint B) (R : H ≃L[ℝ] H) (y s : H) (hs : s ≠ 0) :
    let c := weight R s
    let r := y - B s
    let Pc : H →L[ℝ] H :=
      (⟪c, s⟫_ℝ)⁻¹ • (bracket r c + bracket c r) -
        (⟪r, s⟫_ℝ / ⟪c, s⟫_ℝ ^ 2) • bracket c c
    let obj : (H →L[ℝ] H) → ℝ :=
      fun P => hsNorm b (adjoint (R : H →L[ℝ] H) ∘L P ∘L (R : H →L[ℝ] H))
    Pc ∈ FeasSym b B y s ∧
      (∀ P ∈ FeasSym b B y s, obj Pc ≤ obj P) ∧
      (∀ P ∈ FeasSym b B y s, (∀ Q ∈ FeasSym b B y s, obj P ≤ obj Q) → P = Pc) := by
  intro c r Pc obj
  let z := R.symm s
  let w := adjoint (R : H →L[ℝ] H) r
  let E := fun P : H →L[ℝ] H => adjoint (R : H →L[ℝ] H) ∘L P ∘L (R : H →L[ℝ] H)
  have hz : z ≠ 0 := by
    intro h
    apply hs
    have := congrArg R h
    simpa [z] using this
  have hcs : ⟪c, s⟫_ℝ = ‖z‖ ^ 2 := by
    show ⟪adjoint (R.symm : H →L[ℝ] H) (R.symm s), s⟫_ℝ = _
    rw [adjoint_inner_left]
    exact real_inner_self_eq_norm_sq z
  have hcs0 : ⟪c, s⟫_ℝ ≠ 0 := by rw [hcs]; positivity
  have hRc : adjoint (R : H →L[ℝ] H) c = z := by
    show adjoint (R : H →L[ℝ] H) (adjoint (R.symm : H →L[ℝ] H) z) = z
    rw [← ContinuousLinearMap.comp_apply, ← adjoint_comp]
    have he : (R.symm : H →L[ℝ] H) ∘L (R : H →L[ℝ] H) = ContinuousLinearMap.id ℝ H := by
      ext x; simp
    rw [he, adjoint_id]
    rfl
  have hwz : ⟪w, z⟫_ℝ = ⟪r, s⟫_ℝ := by
    simp [w, z, adjoint_inner_left]
  let Pc' : H →L[ℝ] H :=
    (‖z‖ ^ 2)⁻¹ • (bracket w z + bracket z w) - (⟪w, z⟫_ℝ / ‖z‖ ^ 4) • bracket z z
  have hEPc : E Pc = Pc' := by
    dsimp only [E, Pc, Pc']
    simp only [comp_sub, sub_comp, comp_smul, smul_comp, comp_add, add_comp,
      comp_bracket, bracket_comp, hRc, hcs, hwz]
    congr 2 <;> ring
  have hPcs : Pc s = r := by
    dsimp only [Pc]
    simp only [sub_apply, smul_apply, add_apply, bracket, rankOne_apply]
    match_scalars <;> field_simp <;> ring
  have hPcHS : HSSummable b Pc := by
    exact hs_sub b _ _
      (hs_smul b _ _ (hs_add b _ _ (hsSummable_bracket b _ _) (hsSummable_bracket b _ _)).1).1
      (hs_smul b _ _ (hsSummable_bracket b _ _)).1
  have hPcSA : IsSelfAdjoint Pc := by
    have h1 : IsSelfAdjoint (bracket r c + bracket c r) := by
      show star _ = _
      rw [star_add, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
        bracket, bracket, adjoint_rankOne, adjoint_rankOne, add_comm]
    have h2 : IsSelfAdjoint (bracket c c) := by
      show star _ = _
      rw [ContinuousLinearMap.star_eq_adjoint, bracket, adjoint_rankOne]
    exact ((IsSelfAdjoint.all _).smul h1).sub ((IsSelfAdjoint.all _).smul h2)
  have hPcF : Pc ∈ FeasSym b B y s := by
    refine ⟨hPcHS, hPcSA, ?_⟩
    show (B + Pc) s = y
    rw [add_apply, hPcs]
    simp [r]
  have hEF : ∀ P ∈ FeasSym b B y s, E P ∈ FeasSym b 0 w z := by
    intro P hP
    refine ⟨hs_comp_right b _ _ (hs_comp_left b _ _ hP.1), ?_, ?_⟩
    · show star (E P) = E P
      simp only [E, ContinuousLinearMap.star_eq_adjoint, adjoint_comp, adjoint_adjoint]
      have ha : adjoint P = P := hP.2.1
      rw [ha]
      rfl
    · have hPs : P s = r := by
        have hp : B s + P s = y := hP.2.2
        exact eq_sub_of_add_eq' hp
      simp [E, z, w, hPs]
  have hopt := psb_core b (0 : H →L[ℝ] H) w z hz
  simp only [zero_apply, sub_zero] at hopt
  change Pc' ∈ FeasSym b 0 w z ∧
    (∀ P ∈ FeasSym b 0 w z, hsNorm b Pc' ≤ hsNorm b P) ∧
    (∀ P ∈ FeasSym b 0 w z, (∀ Q ∈ FeasSym b 0 w z, hsNorm b P ≤ hsNorm b Q) → P = Pc') at hopt
  refine ⟨hPcF, ?_, ?_⟩
  · intro P hP
    change hsNorm b (E Pc) ≤ hsNorm b (E P)
    rw [hEPc]
    exact hopt.2.1 (E P) (hEF P hP)
  · intro P hP hmin
    have heq : E P = Pc' := hopt.2.2 (E P) (hEF P hP) (by
      intro Q hQ
      have hle := hmin Pc hPcF
      change hsNorm b (E P) ≤ hsNorm b (E Pc) at hle
      rw [hEPc] at hle
      exact hle.trans (hopt.2.1 Q hQ))
    rw [← hEPc] at heq
    have hback : adjoint (R.symm : H →L[ℝ] H) ∘L adjoint (R : H →L[ℝ] H) = ContinuousLinearMap.id ℝ H := by
      rw [← adjoint_comp]
      have he : (R : H →L[ℝ] H) ∘L (R.symm : H →L[ℝ] H) = ContinuousLinearMap.id ℝ H := by
        ext x; simp
      rw [he, adjoint_id]
    ext x
    have hx := congrArg (fun T : H →L[ℝ] H => adjoint (R.symm : H →L[ℝ] H) (T (R.symm x))) heq
    simp only [E, comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hx
    change (adjoint (R.symm : H →L[ℝ] H) ∘L adjoint (R : H →L[ℝ] H)) (P x) =
      (adjoint (R.symm : H →L[ℝ] H) ∘L adjoint (R : H →L[ℝ] H)) (Pc x) at hx
    simpa only [hback, id_apply] using hx

theorem solution {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H)
    (hB : IsSelfAdjoint B) (y s : H) (hys : 0 < ⟪y, s⟫_ℝ) (C : H ≃L[ℝ] H)
    (hC : y = adjoint (C : H →L[ℝ] H) (C s)) :
    let R : H ≃L[ℝ] H := C.symm
    let r := y - B s
    let Pc : H →L[ℝ] H :=
      (⟪y, s⟫_ℝ)⁻¹ • (bracket r y + bracket y r) - (⟪r, s⟫_ℝ / ⟪y, s⟫_ℝ ^ 2) • bracket y y
    let obj : (H →L[ℝ] H) → ℝ :=
      fun P => hsNorm b (adjoint (R : H →L[ℝ] H) ∘L P ∘L (R : H →L[ℝ] H))
    weight R s = y ∧
      Pc ∈ FeasSym b B y s ∧
      (∀ P ∈ FeasSym b B y s, obj Pc ≤ obj P) ∧
      (∀ P ∈ FeasSym b B y s, (∀ Q ∈ FeasSym b B y s, obj P ≤ obj Q) → P = Pc) := by
  intro R r Pc obj
  have hs : s ≠ 0 := by
    intro h
    simp only [h, inner_zero_right] at hys
    exact lt_irrefl _ hys
  have hc : weight R s = y := by
    simpa only [R, weight, ContinuousLinearEquiv.symm_symm] using hC.symm
  refine ⟨hc, ?_⟩
  have h := accepted_weighted b B hB R y s hs
  dsimp only at h
  rw [hc] at h
  exact h
