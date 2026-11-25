-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.count_cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:38:21.817846+00:00
-- url     : https://prove2.me/submissions/c7d5b33b-948a-498c-a526-363da2399750

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_CountSame
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_CountCross
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
set_option linter.unusedSectionVars false
namespace PositivityTheory.Rg.Cz
section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}
private theorem isWH_coeff_one_polynomial (hT : IsTab col b) (N : ℝ) (c : C) (x : Q)
    (hx : ∃ y ∈ S, col y = c ∧ b y = b x) :
    ∑ y ∈ S.filter (fun y => col y = c), (if b y = b x then N else 0) = N := by
  obtain ⟨y, hyS, hyc, hyb⟩ := hx
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_filter]
  have e : (S.filter fun z => col z = c ∧ b z = b x) = {y} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hzc, hzb⟩
      exact hT.1 z y (hzc.trans hyc.symm) (hzb.trans hyb.symm)
    · rintro rfl
      exact ⟨hyS, hyc, hyb⟩
  rw [e, Finset.card_singleton, one_smul]
private theorem sum_filter_col_le_sum_ite_of_bound (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S))
    (R : Q → Q → ℝ) (N : ℝ) (hsymm : ∀ p q, R p q = R q p)
    (hcross : ∀ p ∈ S, ∀ c, c ≠ col p → ∑ q ∈ S.filter (fun q => col q = c), R p q ≤ N)
    (c d : C) (hcd : c ≠ d) :
    ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d), R p q ≤
      ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d),
        (if b q = b p then N else 0) := by
  by_cases h : ∀ p ∈ S, col p = c → ∃ q ∈ S, col q = d ∧ b q = b p
  · refine Finset.sum_le_sum fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [isWH_coeff_one_polynomial hT N d p (h p hp.1 hp.2)]
    exact hcross p hp.1 d (by rw [hp.2]; exact Ne.symm hcd)
  · push_neg at h
    obtain ⟨p0, hp0S, hp0c, hp0⟩ := h
    have h' : ∀ q ∈ S, col q = d → ∃ p ∈ S, col p = c ∧ b p = b q := by
      intro q hqS hqd
      rcases lt_trichotomy (b p0) (b q) with hl | he | hg
      · obtain ⟨p, hpc, hpb⟩ := hT.2 p0 (b q) hl
        exact ⟨p, (hS p p0 hpc).2 hp0S, hpc.trans hp0c, hpb⟩
      · exact absurd he.symm (hp0 q hqS hqd)
      · obtain ⟨q', hq'c, hq'b⟩ := hT.2 q (b p0) hg
        exact absurd hq'b (hp0 q' ((hS q' q hq'c).2 hqS) (hq'c.trans hqd))
    rw [Finset.sum_comm, Finset.sum_comm (s := S.filter (fun p => col p = c))]
    refine Finset.sum_le_sum fun q hq => ?_
    rw [Finset.mem_filter] at hq
    have e : ∑ p ∈ S.filter (fun p => col p = c), (if b q = b p then N else 0) = N :=
      (Finset.sum_congr rfl fun p _ => if_congr eq_comm rfl rfl).trans
        (isWH_coeff_one_polynomial hT N c q (h' q hq.1 hq.2))
    rw [e, Finset.sum_congr rfl fun p _ => hsymm p q]
    exact hcross q hq.1 c (by rw [hq.2]; exact hcd)
private theorem sum_sum_ite_col_ne_eq_sum_by_col (F : Q → Q → ℝ) :
    ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p then F p q else 0) =
      ∑ c ∈ S.image col, ∑ d ∈ S.image col, (if d ≠ c then
        ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d), F p q else 0) := by
  symm
  calc ∑ c ∈ S.image col, ∑ d ∈ S.image col, (if d ≠ c then
        ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d), F p q else 0)
      = ∑ c ∈ S.image col, ∑ d ∈ S.image col, ∑ p ∈ S.filter (fun p => col p = c),
          ∑ q ∈ S.filter (fun q => col q = d), (if col q ≠ col p then F p q else 0) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        split_ifs with h
        · refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
          rw [Finset.mem_filter] at hp hq
          rw [if_pos (by rw [hp.2, hq.2]; exact h)]
        · symm
          refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
          rw [Finset.mem_filter] at hp hq
          rw [if_neg (by rw [hp.2, hq.2]; exact h)]
    _ = ∑ c ∈ S.image col, ∑ p ∈ S.filter (fun p => col p = c), ∑ d ∈ S.image col,
          ∑ q ∈ S.filter (fun q => col q = d), (if col q ≠ col p then F p q else 0) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p then F p q else 0) := by
        rw [Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem col hp)]
        refine Finset.sum_congr rfl fun p _ => ?_
        exact Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem col hq) _
end
end PositivityTheory.Rg.Cz
end

set_option autoImplicit false
open Finset
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S)) (R : Q → Q → ℝ) (N : ℝ)
    (hsymm : ∀ p q, R p q = R q p)
    (hcross : ∀ p ∈ S, ∀ c, c ≠ col p → ∑ q ∈ S.filter (fun q => col q = c), R p q ≤ N) :
    ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p then R p q else 0) ≤
      ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p ∧ b q = b p then N else 0) := by
  rw [sum_sum_ite_col_ne_eq_sum_by_col (S := S) (col := col) R]
  have hR : ∀ p q, (if col q ≠ col p ∧ b q = b p then N else 0) =
      (if col q ≠ col p then (if b q = b p then N else 0) else 0) := by
    intro p q
    by_cases h1 : col q ≠ col p <;> by_cases h2 : b q = b p <;> simp [h1, h2]
  simp_rw [hR]
  have e2 := sum_sum_ite_col_ne_eq_sum_by_col (S := S) (col := col) (fun p q => if b q = b p then N else 0)
  beta_reduce at e2
  rw [e2]
  refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => ?_
  split_ifs with h
  · exact sum_filter_col_le_sum_ite_of_bound hT hS R N hsymm hcross c d (Ne.symm h)
  · exact le_rfl
end PositivityTheory.Rg.Cz
