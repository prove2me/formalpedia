-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundHighTypes.exists_kind
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:28:11.00545+00:00
-- url     : https://prove2.me/submissions/9ac8f944-3b1a-420e-90ed-27e8bd4fe352

import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Basic


namespace Sensitivity213981Formal
section
/- The finite high-head type system depends only on exact guard counts.
It covers both equal-threshold and symmetric min/max targets, through any
fixed maximum tolerance. The cases q=2 and q=3 have 8 and 11 types. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace ThreeBoundHighTypes











theorem exists_kind (q d : ℕ) (P G : ℕ → Prop)
    (hp : ∀ b, P b → b ≤  q ∧ d=b)
    (hg : ∀ b, G b → b ≤  q ∧ d=b+1)
    (h : (∃ b, P b) ∨ ∃ b, G b) : ∃ k : Kind q, OfKind q P G k := by
  classical
  rcases h with ⟨b,hb⟩ | ⟨b,hb⟩
  · obtain ⟨hbq,hbd⟩ := hp b hb
    by_cases hz : b=0
    · subst b
      refine ⟨⟨0,by omega⟩,?_⟩
      simp only [OfKind,Fin.val_mk,Nat.zero_le,ite_true,true_or,and_true]
      simpa only [hz] using hb
    · by_cases hh : G (b-1)
      · refine ⟨⟨2*q+1+b,by omega⟩,?_⟩
        have h1 : ¬ 2*q+1+b ≤  q := by omega
        have h2 : ¬ 2*q+1+b ≤  2*q+1 := by omega
        have he1 : 2*q+1+b-(2*q+1)=b := by omega
        have he2 : 2*q+1+b-(2*q+2)=b-1 := by omega
        simpa only [OfKind,Fin.val_mk,if_neg h1,if_neg h2,he1,he2] using And.intro hb hh
      · refine ⟨⟨b,by omega⟩,?_⟩
        simp only [OfKind,Fin.val_mk,if_pos hbq]
        exact ⟨hb,Or.inr hh⟩
  · obtain ⟨hbq,hbd⟩ := hg b hb
    by_cases hlast : b=q
    · subst b
      refine ⟨⟨2*q+1,by omega⟩,?_⟩
      have h1 : ¬ 2*q+1 ≤  q := by omega
      have he : 2*q+1-(q+1)=q := by omega
      simp [OfKind,h1,he,hb]
    · by_cases hh : P (b+1)
      · refine ⟨⟨2*q+2+b,by omega⟩,?_⟩
        have h1 : ¬ 2*q+2+b ≤  q := by omega
        have h2 : ¬ 2*q+2+b ≤  2*q+1 := by omega
        have he1 : 2*q+2+b-(2*q+1)=b+1 := by omega
        have he2 : 2*q+2+b-(2*q+2)=b := by omega
        simpa only [OfKind,Fin.val_mk,if_neg h1,if_neg h2,he1,he2] using And.intro hh hb
      · refine ⟨⟨q+1+b,by omega⟩,?_⟩
        have h1 : ¬ q+1+b ≤  q := by omega
        have h2 : q+1+b ≤  2*q+1 := by omega
        have he1 : q+1+b-(q+1)=b := by omega
        have he2 : q+1+b-q=b+1 := by omega
        simp only [OfKind,Fin.val_mk,if_neg h1,if_pos h2,he1,he2]
        exact ⟨hb,Or.inr hh⟩











end ThreeBoundHighTypes




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (q d : Nat) (P G : Nat → Prop) (hp : ∀ (b : Nat), P b → And (@LE.le.{0} Nat instLENat b q) (@Eq.{1} Nat d b))
  (hg :
    ∀ (b : Nat),
      G b →
        And (@LE.le.{0} Nat instLENat b q)
          (@Eq.{1} Nat d
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (h : Or (@Exists.{1} Nat fun (b : Nat) => P b) (@Exists.{1} Nat fun (b : Nat) => G b)),
  @Exists.{1} (Sensitivity213981Formal.ThreeBoundHighTypes.Kind q)
    fun (k : Sensitivity213981Formal.ThreeBoundHighTypes.Kind q) =>
    Sensitivity213981Formal.ThreeBoundHighTypes.OfKind q P G k := @Sensitivity213981Formal.ThreeBoundHighTypes.exists_kind
