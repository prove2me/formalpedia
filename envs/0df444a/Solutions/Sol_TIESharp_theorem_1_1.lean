-- Prove2me | solution 1 for TIESharp.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T03:22:57.269015+00:00
-- url     : https://prove2.me/submissions/e20b9816-6608-433c-8daf-2d979ff0546f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TIESharp_rho
import Theorems.Thm_TIESharp_theorem_3_2
import Theorems.Thm_TIESharp_theorem_3_3

set_option autoImplicit false

namespace TIESharp

theorem _root_.solution (n : ℕ) (hn : 7 ≤ n) :
    rho n = ((n : ℝ) + 1) / 2 ∧
      ∃ F : Family n, IsFeasible F ∧ IsTIE F ∧ IsRApprox F (((n : ℝ) + 1) / 2) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have h3 := theorem_3_3 n hn2
  let F : Family n :=
    { alloc := fun m b =>
        if hb : Nonneg b then Classical.choose (h3.1 m b hb)
        else fun _ => 0
      pay := fun m b i => ∑ j, bsPay b i j }
  have hFlaw : ∀ (m : ℕ) (b : Fin n → Fin m → ℝ), Nonneg b →
      IsBSSlotLaw b (F.alloc m b) ∧ ∀ i, F.pay m b i = ∑ j, bsPay b i j := by
    intro m b hb
    constructor
    · simpa [F, hb] using Classical.choose_spec (h3.1 m b hb)
    · intro i
      rfl
  have hFF : IsFeasible F := by
    intro m b hb
    have hlaw : IsBSSlotLaw b (F.alloc m b) := (hFlaw m b hb).1
    unfold IsBSSlotLaw at hlaw
    exact ⟨hlaw.1, hlaw.2.1⟩
  have hFT : IsTIE F := h3.2.1 F hFlaw
  have hFA : IsRApprox F (((n : ℝ) + 1) / 2) := by
    intro m t ht
    exact (h3.2.2.2 m t (F.alloc m t) ht (hFlaw m t ht).1).1 hn
  have hmem : ((n : ℝ) + 1) / 2 ∈
      {R : ℝ | ∃ G : Family n, IsFeasible G ∧ IsTIE G ∧ IsRApprox G R} :=
    ⟨F, hFF, hFT, hFA⟩
  have hlower : ∀ R ∈
      {R : ℝ | ∃ G : Family n, IsFeasible G ∧ IsTIE G ∧ IsRApprox G R},
      ((n : ℝ) + 1) / 2 ≤ R := by
    intro R hR
    rcases hR with ⟨G, hGF, hGT, hGR⟩
    exact theorem_3_2 n hn1 G R hGF hGT hGR
  have hrho : rho n = ((n : ℝ) + 1) / 2 := by
    unfold rho
    apply le_antisymm
    · apply csInf_le
      · refine ⟨((n : ℝ) + 1) / 2, ?_⟩
        intro R hR
        exact hlower R hR
      · exact hmem
    · apply le_csInf
      · exact ⟨_, hmem⟩
      · intro R hR
        exact hlower R hR
  exact ⟨hrho, ⟨F, hFF, hFT, hFA⟩⟩

end TIESharp
