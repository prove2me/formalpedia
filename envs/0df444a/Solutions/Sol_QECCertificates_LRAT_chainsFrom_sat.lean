-- Prove2me | solution 1 for QECCertificates.LRAT.chainsFrom_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:08.421726+00:00
-- url     : https://prove2.me/submissions/2e655752-7784-4ea6-b5b5-47565ec13bde

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_xorChain_sat
public import Theorems.Thm_QECCertificates_LRAT_dotS_map
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ : Assign} {f : Nat → Nat} {rows : List (List Nat)}
    (hne : ∀ r ∈ rows, r ≠ []) :
    ∀ c, (∀ C ∈ (chainsFrom f rows c).1, SatClause σ C) →
      ∀ r ∈ rows, dotS (fun t => σ (f t)) r = false := by
  induction rows with
  | nil => intro c h r hr; exact absurd hr (List.not_mem_nil)
  | cons r₀ rest ih =>
      intro c h r hr
      rcases List.mem_cons.mp hr with hmem | hr
      · rw [hmem]
        have hcl : ∀ C ∈ (xorChain (r₀.map f) false c).1, SatClause σ C :=
          fun C hC => h C (by simp only [chainsFrom]; exact List.mem_append_left _ hC)
        obtain ⟨x₀, rest₀, hx₀⟩ : ∃ x₀ rest₀, r₀.map f = x₀ :: rest₀ := by
          cases hm : r₀.map f with
          | nil => exact absurd (List.map_eq_nil_iff.mp hm) (hne r₀ (List.mem_cons_self ..))
          | cons x₀ rest₀ => exact ⟨x₀, rest₀, rfl⟩
        have hcl' : ∀ C ∈ (xorChainAux rest₀ false x₀ c).1, SatClause σ C := by
          rw [hx₀] at hcl
          simpa only [xorChain] using hcl
        have hsat : dotS σ (x₀ :: rest₀) = false :=
          xorChain_sat (want := false) (start := c) hcl'
        simpa only [← hx₀, dotS_map σ f r₀] using hsat
      · set c' := (xorChain (r₀.map f) false c).2 with hc'
        have hrest : ∀ C ∈ (chainsFrom f rest c').1, SatClause σ C := by
          intro C hC
          have hmem2 : C ∈ (chainsFrom f (r₀ :: rest) c).1 := by
            simp only [chainsFrom]
            exact List.mem_append_right _ (hc' ▸ hC)
          exact h C hmem2
        exact ih (fun r' hr' => hne r' (List.mem_cons_of_mem _ hr')) c' hrest r hr
end QECCertificates.LRAT
