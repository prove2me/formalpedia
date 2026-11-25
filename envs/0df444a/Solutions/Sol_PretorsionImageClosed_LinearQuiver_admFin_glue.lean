-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.admFin_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:26:47.496986+00:00
-- url     : https://prove2.me/submissions/ee584801-fb48-41fc-b290-ea0c8d5aba33

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {D : IntervalFamily n} {J : Finset (Fin (n + 1))} (hJ : J ⊆ adm D) :
    admFin (D.glue J) = J ∪ (adm D).filter (fun c => ∀ a ∈ J, c ≤ a) := by
  ext c
  rw [mem_admFin, Finset.mem_union, Finset.mem_filter]
  -- the condition on old intervals is admissibility for `D`
  have hold : (∀ a d : Fin n, (a, d) ∈ D.D → a.castSucc ≤ c → c ≤ d.castSucc →
      (c, d.castSucc) ∈ (D.glue J).D) ↔ c ∈ adm D := by
    induction c using Fin.lastCases with
    | last =>
      refine ⟨fun _ => last_mem_adm D, fun _ a d _ _ h => ?_⟩
      exact absurd h (not_le.2 (Fin.castSucc_lt_last d))
    | cast c =>
      rw [castSucc_mem_adm, mem_admFin]
      constructor
      · intro h p hp h1 h2
        exact mem_glue_castSucc.1 (h p.1 p.2 hp (Fin.castSucc_le_castSucc_iff.2 h1)
          (Fin.castSucc_le_castSucc_iff.2 h2))
      · intro h a d had h1 h2
        exact mem_glue_castSucc.2 (h (a, d) had (Fin.castSucc_le_castSucc_iff.1 h1)
          (Fin.castSucc_le_castSucc_iff.1 h2))
  constructor
  · intro h
    by_cases hcJ : c ∈ J
    · exact Or.inl hcJ
    · right
      refine ⟨hold.1 fun a d had h1 h2 => h _ (mem_glue_castSucc.2 had) h1 h2, ?_⟩
      intro a ha
      by_contra hlt
      have := h (a, Fin.last n) (mem_glue_last.2 ha) (not_le.1 hlt).le (Fin.le_last _)
      exact hcJ (mem_glue_last.1 this)
  · intro h p hp h1 h2
    rw [mem_glue] at hp
    rcases hp with ⟨a, d, rfl, had⟩ | ⟨hp2, hp1⟩
    · have hc : c ∈ adm D := by
        rcases h with hcJ | ⟨hc, -⟩
        · exact hJ hcJ
        · exact hc
      exact hold.2 hc a d had h1 h2
    · rw [hp2] at h2 ⊢
      rw [mem_glue_last]
      rcases h with hcJ | ⟨-, hle⟩
      · exact hcJ
      · have := le_antisymm h1 (hle p.1 hp1)
        rw [← this]
        exact hp1
end PretorsionImageClosed.LinearQuiver
