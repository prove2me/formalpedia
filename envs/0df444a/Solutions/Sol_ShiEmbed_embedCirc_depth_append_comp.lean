-- Prove2me | solution 1 for ShiEmbed.embedCirc_depth_append_comp
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T18:13:36.895442+00:00
-- url     : https://prove2.me/submissions/b6f1bb16-6c12-4cb1-9eae-b0e8e2b16b7f

-- Three structural laws of `ShiEmbed.embedCirc`.
import Definitions.Def_ShiEmbed_Core

set_option autoImplicit false

open ShiShallow

/-- Pointwise functoriality on one instruction (`cnot` proof by proof irrelevance). -/
private theorem shiEmb_instr_comp {m n p : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (f : Fin n → Fin p) (hf : Function.Injective f) (i : Instr m) :
    ShiEmbed.embedInstr (f ∘ e) (hf.comp he) i
      = ShiEmbed.embedInstr f hf (ShiEmbed.embedInstr e he i) := by
  cases i
  all_goals first
    | rfl
    | simp [ShiEmbed.embedInstr, Function.comp]

/-- Functoriality on one layer. -/
private theorem shiEmb_layer_comp {m n p : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (f : Fin n → Fin p) (hf : Function.Injective f) (l : List (Instr m)) :
    ShiEmbed.embedLayer (f ∘ e) (hf.comp he) l
      = ShiEmbed.embedLayer f hf (ShiEmbed.embedLayer e he l) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have hh : ShiEmbed.embedInstr (f ∘ e) (hf.comp he) a
          = ShiEmbed.embedInstr f hf (ShiEmbed.embedInstr e he a) :=
        shiEmb_instr_comp e he f hf a
      show ShiEmbed.embedInstr (f ∘ e) (hf.comp he) a
            :: ShiEmbed.embedLayer (f ∘ e) (hf.comp he) t
          = ShiEmbed.embedInstr f hf (ShiEmbed.embedInstr e he a)
            :: ShiEmbed.embedLayer f hf (ShiEmbed.embedLayer e he t)
      exact congr (congrArg List.cons hh) ih

/-- `embedCirc` preserves `depth`, distributes over `++`, and is functorial in `e`. -/
theorem solution {m n p : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (f : Fin n → Fin p) (hf : Function.Injective f) :
    (∀ c : Layered m, ShiShallow.depth (ShiEmbed.embedCirc e he c) = ShiShallow.depth c)
      ∧ (∀ c₁ c₂ : Layered m, ShiEmbed.embedCirc e he (c₁ ++ c₂)
            = ShiEmbed.embedCirc e he c₁ ++ ShiEmbed.embedCirc e he c₂)
      ∧ (∀ c : Layered m, ShiEmbed.embedCirc (f ∘ e) (hf.comp he) c
            = ShiEmbed.embedCirc f hf (ShiEmbed.embedCirc e he c)) := by
  refine ⟨fun c => ?_, fun c₁ c₂ => ?_, fun c => ?_⟩
  · first
      | exact List.length_map (ShiEmbed.embedLayer e he)
      | simp [ShiShallow.depth, ShiEmbed.embedCirc]
  · first
      | exact List.map_append
      | simp [ShiEmbed.embedCirc]
  · induction c with
    | nil => rfl
    | cons a t ih =>
        have hh : ShiEmbed.embedLayer (f ∘ e) (hf.comp he) a
            = ShiEmbed.embedLayer f hf (ShiEmbed.embedLayer e he a) :=
          shiEmb_layer_comp e he f hf a
        show ShiEmbed.embedLayer (f ∘ e) (hf.comp he) a
              :: ShiEmbed.embedCirc (f ∘ e) (hf.comp he) t
            = ShiEmbed.embedLayer f hf (ShiEmbed.embedLayer e he a)
              :: ShiEmbed.embedCirc f hf (ShiEmbed.embedCirc e he t)
        exact congr (congrArg List.cons hh) ih
