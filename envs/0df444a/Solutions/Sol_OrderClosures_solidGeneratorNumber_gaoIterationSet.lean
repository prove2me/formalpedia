-- Prove2me | solution 1 for OrderClosures.solidGeneratorNumber_gaoIterationSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:27.345689+00:00
-- url     : https://prove2.me/submissions/153391d7-cfbe-405f-a1a9-d9693f54b448

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
public import Theorems.Thm_OrderClosures_gaoGlobalGenerator_index_eq_of_abs_le
public import Theorems.Thm_OrderClosures_mk_gaoGlobalGenerator_range
public import Theorems.Thm_OrderClosures_CNFListLT_trans
public import Theorems.Thm_OrderClosures_CNFStep_trans


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    solidGeneratorNumber (gaoIterationSet κ hκ) = Cardinal.lift.{u + 1, u} κ := by
  classical
  apply le_antisymm
  · calc
      solidGeneratorNumber (gaoIterationSet κ hκ) ≤
          Cardinal.mk (Set.range (gaoGlobalGenerator κ hκ)) := by
        apply csInf_le'
        exact ⟨Set.range (gaoGlobalGenerator κ hκ), rfl, rfl⟩
      _ = Cardinal.lift.{u + 1, u} κ := mk_gaoGlobalGenerator_range κ hκ
  · apply le_csInf
    · exact ⟨Cardinal.mk (Set.range (gaoGlobalGenerator κ hκ)),
        Set.range (gaoGlobalGenerator κ hκ), rfl, rfl⟩
    · intro c hc
      rcases hc with ⟨A, hAc, hAS⟩
      rw [← hAc]
      have hbelow : ∀ a : ULift.{u + 1, u} (Cardinal.ord κ).ToType,
          ∃ x : A, |gaoGlobalGenerator κ hκ a| ≤ |x.1| := by
        intro a
        have hgenS : gaoGlobalGenerator κ hκ a ∈ solidHull A := by
          rw [hAS]
          exact ⟨gaoGlobalGenerator κ hκ a, ⟨a, rfl⟩, le_rfl⟩
        rcases hgenS with ⟨x, hxA, hax⟩
        exact ⟨⟨x, hxA⟩, hax⟩
      choose x hx using hbelow
      have habove : ∀ a : ULift.{u + 1, u} (Cardinal.ord κ).ToType,
          ∃ b : ULift.{u + 1, u} (Cardinal.ord κ).ToType,
            |(x a).1| ≤ |gaoGlobalGenerator κ hκ b| := by
        intro a
        have hxS : (x a).1 ∈ gaoIterationSet κ hκ := by
          rw [← hAS]
          exact ⟨(x a).1, (x a).2, le_rfl⟩
        rcases hxS with ⟨g, ⟨b, rfl⟩, hxb⟩
        exact ⟨b, hxb⟩
      choose b hb using habove
      have hxinj : Function.Injective x := by
        intro a a' haa'
        have hab' : |gaoGlobalGenerator κ hκ a| ≤
            |gaoGlobalGenerator κ hκ (b a')| := by
          calc
            |gaoGlobalGenerator κ hκ a| ≤ |(x a).1| := hx a
            _ = |(x a').1| := by rw [haa']
            _ ≤ |gaoGlobalGenerator κ hκ (b a')| := hb a'
        have ha'b : a' = b a' :=
          gaoGlobalGenerator_index_eq_of_abs_le κ hκ ((hx a').trans (hb a'))
        exact (gaoGlobalGenerator_index_eq_of_abs_le κ hκ hab').trans ha'b.symm
      calc
        Cardinal.lift.{u + 1, u} κ =
            Cardinal.mk (ULift.{u + 1, u} (Cardinal.ord κ).ToType) := by
          change Cardinal.lift.{u + 1, u} κ = Cardinal.lift.{u + 1, u}
            (Cardinal.mk (Cardinal.ord κ).ToType)
          rw [Cardinal.mk_ord_toType]
        _ ≤ Cardinal.mk A := Cardinal.mk_le_of_injective hxinj
end OrderClosures
