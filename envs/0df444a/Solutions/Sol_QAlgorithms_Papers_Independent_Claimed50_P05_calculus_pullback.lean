-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_pullback
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:27:56.444944+00:00
-- url     : https://prove2.me/submissions/d9391b52-df40-4972-8d9e-000c8ddde51c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P05
universe u v w
variable {k : Type*} [RCLike k]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

theorem g58b_pullback (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (T : P05.Symbol Y k → P05.Symbol X k) (hT : SymbolHom T)
    (hbp : ∀ fn f, BP fn f → BP (fun n => T (fn n)) (T f)) :
    Calculus (fun f => F (T f)) := by
  obtain ⟨hcl, ⟨h1, hadd, hsc, hmul, hdom⟩, hbd, hw⟩ := hF
  obtain ⟨Tc, Tp, Tt, Ts⟩ := hT
  have hscal : ∀ (c : k) (f : P05.Symbol Y k), T (scalar c f) = scalar c (T f) := by
    intro c f
    have e1 : scalar c f = times (constant c) f := Subtype.ext rfl
    have e2 : scalar c (T f) = times (constant c) (T f) := Subtype.ext rfl
    rw [e1, e2, Tt, Tc]
  have hbs : ∀ f : P05.Symbol Y k, BoundedSymbol f → BoundedSymbol (T f) := by
    intro f ⟨c, hc⟩
    have : BP (fun _ : ℕ => f) f := ⟨fun x => tendsto_const_nhds, c, fun _ x => hc x⟩
    obtain ⟨-, c', hc'⟩ := hbp _ _ this
    exact ⟨c', fun x => hc' 0 x⟩
  refine ⟨fun f => hcl (T f), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [Tc]; exact h1
  · intro f g; simp only [Tp]; exact hadd _ _
  · intro c f; simp only [hscal]; exact hsc _ _
  · intro f g; simp only [Tt]; exact hmul _ _
  · intro f g; simp only [Tt]; exact hdom _ _
  · intro f hf
    obtain ⟨hb, hadj⟩ := hbd (T f) (hbs f hf)
    exact ⟨hb, by simp only [Ts]; exact hadj⟩
  · intro fn f hbpf
    exact hw _ _ (hbp fn f hbpf)

theorem solution (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (T : P05.Symbol Y k → P05.Symbol X k) (hT : SymbolHom T)
    (hbp : ∀ fn f, BP fn f → BP (fun n => T (fn n)) (T f)) :
    Calculus (fun f => F (T f)) := g58b_pullback F hF T hT hbp
