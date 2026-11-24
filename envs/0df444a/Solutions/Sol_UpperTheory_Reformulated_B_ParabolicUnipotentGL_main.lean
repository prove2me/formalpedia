-- Prove2me | solution 1 for UpperTheory.Reformulated.B.ParabolicUnipotentGL.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:01.900413+00:00
-- url     : https://prove2.me/submissions/3c0ef7bc-1067-4348-af07-72412b2aa81f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ParabolicUnipotentGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UpperTheory.Reformulated.B.ParabolicUnipotentGL
section helpers
variable {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
private theorem U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k := by
  apply Submodule.span_mono
  rintro x ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩
private theorem monomial_mem_filtration_of_length_le (l : List (Fin n × Fin n)) {k : ℕ} (h : l.length ≤ k) : P E l ∈ U E k :=
  Submodule.subset_span ⟨l, h, rfl⟩
private theorem gen_mem (a b : Fin n) : E a b ∈ U E 1 := by
  have := monomial_mem_filtration_of_length_le E [(a, b)] (k := 1) (by simp)
  simpa [P] using this
private theorem mul_mem_U {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y ∈ U E (j + k) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      refine Submodule.subset_span ⟨l ++ m, ?_, ?_⟩
      · simp only [List.length_append]; omega
      · simp
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha
private theorem gen_comm_mem (hE : IsGlRep E) (a b c d : Fin n) :
    E a b * E c d - E c d * E a b ∈ U E 1 := by
  rw [hE a b c d]
  refine sub_mem ?_ ?_
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _
private theorem gen_comm_P (hE : IsGlRep E) (a b : Fin n) (l : List (Fin n × Fin n)) :
    E a b * P E l - P E l * E a b ∈ U E l.length := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : E a b * P E (p :: t) - P E (p :: t) * E a b
        = (E a b * E p.1 p.2 - E p.1 p.2 * E a b) * P E t
          + E p.1 p.2 * (E a b * P E t - P E t * E a b) := by
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e, List.length_cons, add_comm t.length 1]
    exact add_mem (mul_mem_U E (gen_comm_mem E hE _ _ _ _) (monomial_mem_filtration_of_length_le E t le_rfl))
      (mul_mem_U E (gen_mem E _ _) ih)
private theorem monomial_commutator_mem_filtration (hE : IsGlRep E) (l : List (Fin n × Fin n)) (q : Fin n × Fin n)
    (m : List (Fin n × Fin n)) :
    P E l * P E (q :: m) - P E (q :: m) * P E l ∈ U E (l.length + m.length) := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : P E (p :: t) * P E (q :: m) - P E (q :: m) * P E (p :: t)
        = E p.1 p.2 * (P E t * P E (q :: m) - P E (q :: m) * P E t)
          + (E p.1 p.2 * P E (q :: m) - P E (q :: m) * E p.1 p.2) * P E t := by
      generalize P E (q :: m) = y
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e]
    refine add_mem ?_ ?_
    · exact U_mono E (by simp only [List.length_cons]; omega) (mul_mem_U E (gen_mem E _ _) ih)
    · exact U_mono E (by simp only [List.length_cons]; omega)
        (mul_mem_U E (gen_comm_P E hE _ _ (q :: m)) (monomial_mem_filtration_of_length_le E t le_rfl))
end helpers
end UpperTheory.Reformulated.B.ParabolicUnipotentGL
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.ParabolicUnipotentGL
theorem _root_.solution :
    ∀ {n : ℕ} {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
      UpperTheory.Reformulated.B.ParabolicUnipotentGL.IsGlRep E →
        ∀ {j k : ℕ} {x y : Module.End ℂ V},
          x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E j →
            y ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E k → x * y - y * x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E (j + k - (1 : ℕ)) := by
  intro n V _ _ E hE j k x y hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      cases m with
      | nil => simp
      | cons q t =>
        simp only [List.length_cons] at hm
        exact UpperTheory.Reformulated.B.ParabolicUnipotentGL.U_mono E (by omega) (UpperTheory.Reformulated.B.ParabolicUnipotentGL.monomial_commutator_mem_filtration E hE l q t)
    | zero => simp
    | add a b _ _ ha hb =>
      have e : x * (a + b) - (a + b) * x = (x * a - a * x) + (x * b - b * x) := by noncomm_ring
      rw [e]; exact add_mem ha hb
    | smul c a _ ha =>
      have e : x * (c • a) - (c • a) * x = c • (x * a - a * x) := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [e]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb =>
    have e : (a + b) * y - y * (a + b) = (a * y - y * a) + (b * y - y * b) := by noncomm_ring
    rw [e]; exact add_mem ha hb
  | smul c a _ ha =>
    have e : (c • a) * y - y * (c • a) = c • (a * y - y * a) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c ha
end UpperTheory.Reformulated.B.ParabolicUnipotentGL
