-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.fiber_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:54:43.991853+00:00
-- url     : https://prove2.me/submissions/2748faaa-5625-43da-83f9-9e96af2d6f21

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_restrict_glue
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_contOf_subset
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_glue_contOf_colOf
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_contOf_glue
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_colOf_glue
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_cpWeight_glue
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_mem_model_iff
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
theorem _root_.solution (p : CutoffPair n) :
    ∑ x ∈ univ.filter (fun x : CutoffPair (n + 1) => x.restrict = p), cpWeight x =
      C (q ^ middleCount p.1.1 p.1.2) * psi (candRows p) := by
  have h1 : ∑ x ∈ univ.filter (fun x : CutoffPair (n + 1) => x.restrict = p), cpWeight x =
      ∑ y ∈ model p, C (q ^ middleCount p.1.1 p.1.2) *
        (X ^ y.1.card * C (q ^ (y.1.filter (fun a => colValue y.2 ≤ a.val)).card)) := by
    refine Finset.sum_bij' (fun x _ => ⟨contOf x, colOf x⟩)
      (fun y hy => glue p y.1 y.2 (mem_model_iff.1 hy).2) ?_ ?_ ?_ ?_ ?_
    · -- `i` maps the fibre into the model
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [mem_model_iff]
      refine ⟨?_, ?_⟩
      · have := contOf_subset x
        rwa [hx.2] at this
      · have := allowed_colOf x
        rwa [hx.2] at this
    · -- `j` maps the model into the fibre
      intro y hy
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        restrict_glue p y.1 y.2 (mem_model_iff.1 hy).1 (mem_model_iff.1 hy).2⟩
    · -- `j ∘ i = id`
      intro x hx
      rw [Finset.mem_filter] at hx
      have key : ∀ (p' : CutoffPair n) (_ : x.restrict = p') (hc : Allowed p' (contOf x) (colOf x)),
          glue p' (contOf x) (colOf x) hc = x := by
        rintro _ rfl hc
        exact glue_contOf_colOf x
      exact key p hx.2 _
    · -- `i ∘ j = id`
      rintro ⟨Cont, c⟩ hy
      simp only [Sigma.mk.injEq, heq_eq_eq]
      exact ⟨contOf_glue p Cont c _, colOf_glue p Cont c _⟩
    · -- the weights agree
      intro x hx
      rw [Finset.mem_filter] at hx
      have key : ∀ (p' : CutoffPair n) (_ : x.restrict = p') (hc : Allowed p' (contOf x) (colOf x)),
          cpWeight x = C (q ^ middleCount p'.1.1 p'.1.2) *
            (X ^ (contOf x).card *
              C (q ^ ((contOf x).filter (fun a => colValue (colOf x) ≤ a.val)).card)) := by
        rintro _ rfl hc
        rw [← cpWeight_glue x.restrict (contOf x) (colOf x) (contOf_subset x) hc,
          glue_contOf_colOf x]
      exact key p hx.2 (by have := allowed_colOf x; rwa [hx.2] at this)
  rw [h1, model, Finset.sum_sigma, psi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Cont _
  rw [choices, Finset.sum_insert (by simp), Finset.sum_image (fun _ _ _ _ h => Option.some_injective _ h)]
  have h0 : Cont.filter (fun a : Fin (n + 1) => colValue (none : Option (Fin (n + 1))) ≤ a.val) =
      Cont :=
    Finset.filter_true_of_mem (fun _ _ => Nat.zero_le _)
  have hs : ∀ e : Fin (n + 1), Cont.filter (fun a : Fin (n + 1) => colValue (some e) ≤ a.val) =
      Cont.filter (fun a => e < a) :=
    fun e => Finset.filter_congr (fun a _ => Iff.rfl)
  dsimp only
  simp only [h0, hs, psiTerm, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr
  · ext e
    simp only [Finset.mem_filter]
  · intros
    rfl
end PretorsionImageClosed.LinearQuiver
