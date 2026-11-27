-- Prove2me | solution 1 for SizeRamsey.Plan.tight_subcubic_chordless
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:55.938049+00:00
-- url     : https://prove2.me/submissions/be222729-2ea3-4cea-9341-fe82f2a21065

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Equality_Common
public import Theorems.Thm_SizeRamsey_Plan_subcubic_chord_reduction
public import Theorems.Thm_SizeRamsey_Plan_universal

section
@[expose] public section
namespace SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
private theorem tight_subcubic_no_chord02
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (ht : Tight G)
    (hmax : ∀ v, G.degree v ≤ 3)
    (f : Fin 4 → V) (hf : IsC4Map G f) :
    ¬ G.Adj (f 0) (f 2) := by
  intro hac
  obtain ⟨hτ, hcount, hdeg⟩ := subcubic_chord_reduction G hmax f hf hac
  have hA := universal (erase G {f 0, f 1, f 2})
  unfold Tight at ht
  omega
end SizeRamsey.Plan
end
end

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (ht : Tight G)
    (hmax : ∀ v, G.degree v ≤ 3)
    (f : Fin 4 → V) (hf : IsC4Map G f) :
    ¬ G.Adj (f 0) (f 2) ∧
    ¬ G.Adj (f 1) (f 3) := by
  refine ⟨tight_subcubic_no_chord02 G ht hmax f hf, ?_⟩
  obtain ⟨hinj, h01, h12, h23, h30⟩ := hf
  have hg : IsC4Map G ![f 1, f 2, f 3, f 0] := by
    refine ⟨?_, by simpa using h12, by simpa using h23, by simpa using h30,
      by simpa using h01⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hinj.eq_iff]
  simpa using tight_subcubic_no_chord02 G ht hmax _ hg
end SizeRamsey.Plan
