-- Prove2me | solution 1 for SmaleNinth.smale_ninth_real_ram_rational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T03:09:10.893897+00:00
-- url     : https://prove2.me/submissions/4766ffc7-f641-424a-84bd-f9e8f44aaba9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_Optimization_LinearProgramming_strongly_polynomial_feasibility
import Theorems.Thm_SmaleNinth_real_ram_of_oai_program
import Mathlib.Data.Rat.Cast.Order

open Matrix LinearOptimization OAI.Optimization.LinearProgramming

namespace SmaleNinth.RatTransfer

/-- A rational machine state viewed over the reals. -/
def castState (s : RAM.State ℚ) : RAM.State ℝ where
  pc := s.pc
  data j := (s.data j : ℝ)
  index := s.index
  output := s.output

@[simp] theorem castState_pc (s : RAM.State ℚ) : (castState s).pc = s.pc := rfl
@[simp] theorem castState_index (s : RAM.State ℚ) : (castState s).index = s.index := rfl
@[simp] theorem castState_output (s : RAM.State ℚ) : (castState s).output = s.output := rfl
@[simp] theorem castState_data (s : RAM.State ℚ) (j : ℕ) : (castState s).data j = (s.data j : ℝ) :=
  rfl

theorem castState_putData (s : RAM.State ℚ) (d : ℕ) (x : ℚ) :
    castState (s.putData d x) = (castState s).putData d (x : ℝ) := by
  simp only [castState, RAM.State.putData]
  congr 1
  exact Function.comp_update (fun q : ℚ => (q : ℝ)) s.data d x

theorem castState_putIndex (s : RAM.State ℚ) (d x : ℕ) :
    castState (s.putIndex d x) = (castState s).putIndex d x := rfl

theorem castState_setPc (s : RAM.State ℚ) (n : ℕ) :
    castState { s with pc := n } = { castState s with pc := n } := rfl

theorem castState_setOutput (s : RAM.State ℚ) (o : Option ℕ) :
    castState { s with output := o } = { castState s with output := o } := rfl

theorem execInstr_cast (i : RAM.Instr) (s : RAM.State ℚ) :
    (RAM.execInstr i s).map castState = RAM.execInstr i (castState s) := by
  cases i with
  | div d a b =>
    by_cases h : s.data b = 0
    · simp [RAM.execInstr, h]
    · simp [RAM.execInstr, h, castState_putData]
  | branchLT a b yes no =>
    simp only [RAM.execInstr, Option.map_some, castState_setPc, castState_data, Rat.cast_lt]
  | branchAddrLT a b yes no => rfl
  | jump target => rfl
  | halt tag => rfl
  | _ => simp [RAM.execInstr, castState_putData, castState_putIndex]

theorem step_cast (p : RAM.Program) (s : RAM.State ℚ) :
    (RAM.step p s).map castState = RAM.step p (castState s) := by
  unfold RAM.step
  rcases s with ⟨pc, data, index, output⟩
  cases output with
  | some o => rfl
  | none =>
    cases h : p[pc]? with
    | none => simp [castState, h]
    | some i => simpa [castState, h] using execInstr_cast i ⟨pc, data, index, none⟩

theorem trace_cast {p : RAM.Program} {s : RAM.State ℚ} {k : ℕ} {t : Fin (k + 1) → RAM.State ℚ}
    (h : RAM.Trace p s k t) : RAM.Trace p (castState s) k (fun i => castState (t i)) := by
  refine ⟨show castState (t 0) = castState s by rw [h.1], fun i => ?_⟩
  rw [← step_cast, h.2 i]
  rfl

theorem lpInput_cast {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    (lpInput A b).map ((↑) : ℚ → ℝ) = lpInput (A.map ((↑) : ℚ → ℝ)) (fun i => (b i : ℝ)) := by
  simp [lpInput, List.map_flatten, List.map_ofFn, Function.comp_def]
  rfl

theorem start_cast {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    castState (RAM.start [m, d] (lpInput A b)) =
      RAM.start [m, d] (lpInput (A.map ((↑) : ℚ → ℝ)) (fun i => (b i : ℝ))) := by
  rw [← lpInput_cast]
  simp only [castState, RAM.start, RAM.State.mk.injEq, true_and, and_true]
  funext j
  rw [List.getElem?_map]
  cases (lpInput A b)[j]? <;> simp

/-- The easy direction of Farkas' lemma over `ℝ`. -/
theorem infeasible_of_farkas {m d : ℕ} {A : Matrix (Fin m) (Fin d) ℝ} {b y : Fin m → ℝ}
    (hy0 : 0 ≤ y) (hAy : A.transpose *ᵥ y = 0) (hby : b ⬝ᵥ y < 0) (x : Fin d → ℝ)
    (hx : Feasible A b x) : False := by
  have h1 : y ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hx hy0
  have h2 : y ⬝ᵥ (A *ᵥ x) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hAy, zero_dotProduct]
  rw [dotProduct_comm] at hby
  linarith

theorem readVector_cast (s : RAM.State ℚ) (o n : ℕ) :
    readVector (castState s) o n = fun i => ((readVector s o n i : ℚ) : ℝ) := rfl

/-- Rational feasibility output gives the correct real verdict. -/
theorem tag_correct {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (s : RAM.State ℚ)
    (h : FeasibilityOutput A b s) :
    ∃ tag : ℕ, (castState s).output = some tag ∧
      (tag = 0 ↔ ∃ x, Feasible (A.map ((↑) : ℚ → ℝ)) (fun i => (b i : ℝ)) x) := by
  rcases h with ⟨h0, hx⟩ | ⟨h1, hy0, hAy, hby, -⟩
  · refine ⟨0, h0, iff_of_true rfl ⟨fun i => ((readVector s 0 d i : ℚ) : ℝ), ?_⟩⟩
    intro i
    have := hx i
    simp only [mulVec, dotProduct, Matrix.map_apply] at this ⊢
    rw [← Rat.cast_le (K := ℝ)] at this
    push_cast at this
    exact this
  · refine ⟨1, h1, iff_of_false (by decide) ?_⟩
    rintro ⟨x, hx⟩
    set y := readVector s 0 m
    refine infeasible_of_farkas (y := fun i => ((y i : ℚ) : ℝ)) ?_ ?_ ?_ x hx
    · intro i
      show (0 : ℝ) ≤ ((y i : ℚ) : ℝ)
      exact_mod_cast hy0 i
    · funext j
      have := congrFun hAy j
      simp only [mulVec, dotProduct, transpose_apply, Matrix.map_apply, Pi.zero_apply] at this ⊢
      exact_mod_cast this
    · simp only [dotProduct] at hby ⊢
      exact_mod_cast hby

end SmaleNinth.RatTransfer

open SmaleNinth.RatTransfer in
theorem solution :
    ∃ (R : SmaleNinth.RAMProgram) (C d : ℕ),
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        ∃ result : Bool,
          SmaleNinth.RAMDecidesInTime R
            (SmaleNinth.encodeLP (A.map ((↑) : ℚ → ℝ)) (fun i => (b i : ℝ)))
            (C * (m * n + m + 2) ^ d) result ∧
          (result = true ↔
            (polyhedron (A.map ((↑) : ℚ → ℝ)) (fun i => (b i : ℝ))).Nonempty) := by
  have hOAI := strongly_polynomial_feasibility
  unfold StronglyPolynomialFeasibility at hOAI
  obtain ⟨p, c, e, bC, bE, hp⟩ := hOAI
  obtain ⟨R, C, d, hR⟩ := SmaleNinth.real_ram_of_oai_program p c e
  refine ⟨R, C, d, fun m n A b => hR m n _ _ fun hm hn => ?_⟩
  obtain ⟨k, t, htr, hk, -, hout⟩ := hp m n hm hn (-A) (-b)
  refine ⟨k, fun i => castState (t i), ?_, hk, ?_⟩
  · have := trace_cast htr
    rw [start_cast] at this
    convert this using 3 <;> ext <;> simp
  · obtain ⟨tag, htag, hiff⟩ := tag_correct (-A) (-b) _ hout
    refine ⟨tag, htag, ?_⟩
    convert hiff using 4 <;> ext <;> simp
