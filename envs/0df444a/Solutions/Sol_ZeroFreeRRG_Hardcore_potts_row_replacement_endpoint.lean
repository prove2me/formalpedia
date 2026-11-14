-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_row_replacement_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:22:59.959715+00:00
-- url     : https://prove2.me/submissions/fe1b748a-c1a5-4d51-8a37-8c1688a685ff

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsRowChain
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (S : Finset V) (τ : V → Fin q) (v : V) (hv : v ∉ S) (a b : Fin q)
    (hW' : ∀ e i j, pottsReplaceRows W (G.incidenceFinset v) a b e i j =
      pottsReplaceRows W (G.incidenceFinset v) a b e j i) :
    pottsWeightedPartial q G (pottsReplaceRows W (G.incidenceFinset v) a b) hW'
      (insert v S) (Function.update τ v a) =
    pottsWeightedPartial q G W hW (insert v S) (Function.update τ v b) := by
  classical
  let T := fun σ : V → Fin q => Function.update σ v ((Equiv.swap a b) (σ v))
  have hTinv : Function.Involutive T := by
    intro σ
    funext x
    by_cases hx : x=v
    · subst x
      simp [T]
    · simp [T,Function.update_of_ne hx]
  let E := Equiv.ofBijective T hTinv.bijective
  have hpred (σ : V → Fin q) :
      (∀ x ∈ insert v S, σ x = Function.update τ v a x) ↔
      (∀ x ∈ insert v S, T σ x = Function.update τ v b x) := by
    constructor
    · intro h x hx
      rcases Finset.mem_insert.mp hx with hvx | hx
      · subst x
        have hσ : σ v = a := by simpa using h v (Finset.mem_insert_self _ _)
        simp [T,hσ]
      · have hxv : x ≠ v := by intro h'; subst x; exact hv hx
        have hσ := h x (Finset.mem_insert_of_mem hx)
        simpa [T,Function.update_of_ne hxv] using hσ
    · intro h x hx
      rcases Finset.mem_insert.mp hx with hvx | hx
      · subst x
        have hσ : (Equiv.swap a b) (σ v) = b := by simpa [T] using h v (Finset.mem_insert_self _ _)
        have : σ v = a := by
          have hh := congrArg (Equiv.swap a b) hσ
          simpa using hh
        simpa using this
      · have hxv : x ≠ v := by intro h'; subst x; exact hv hx
        have hσ := h x (Finset.mem_insert_of_mem hx)
        simpa [T,Function.update_of_ne hxv] using hσ
  have hweight (σ : V → Fin q) (hσv : σ v=a) (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      pottsEdgeWeight (pottsReplaceRows W (G.incidenceFinset v) a b) hW' σ e =
        pottsEdgeWeight W hW (T σ) e := by
    refine Sym2.inductionOn e ?_ he
    intro x y he'
    have hadj : G.Adj x y := by simpa using he'
    have hxy : x ≠ y := G.ne_of_adj hadj
    by_cases hxv : x=v
    · subst x
      have hyv : y ≠ v := Ne.symm hxy
      have heF : s(v,y) ∈ G.incidenceFinset v := by simpa using hadj
      change pottsReplaceRows W (G.incidenceFinset v) a b s(v,y) (σ v) (σ y) = W s(v,y) (T σ v) (T σ y)
      simp [pottsReplaceRows,heF,hσv,T,Function.update_of_ne hyv]
    · by_cases hyv : y=v
      · subst y
        have heF : s(x,v) ∈ G.incidenceFinset v := by
          rw [Sym2.eq_swap]
          simpa using hadj.symm
        change pottsReplaceRows W (G.incidenceFinset v) a b s(x,v) (σ x) (σ v) = W s(x,v) (T σ x) (T σ v)
        by_cases hxa : σ x=a
        · simp [pottsReplaceRows,heF,hσv,T,Function.update_of_ne hxv,hxa,hW]
        · simp [pottsReplaceRows,heF,hσv,T,Function.update_of_ne hxv,hxa,hW]
      · have heF : s(x,y) ∉ G.incidenceFinset v := by
          rw [G.incidenceFinset_eq_filter]
          simp [Sym2.mem_iff,hxv,hyv,Ne.symm hxv,Ne.symm hyv]
        change pottsReplaceRows W (G.incidenceFinset v) a b s(x,y) (σ x) (σ y) = W s(x,y) (T σ x) (T σ y)
        simp [pottsReplaceRows,heF,T,Function.update_of_ne hxv,Function.update_of_ne hyv]
  unfold pottsWeightedPartial
  apply Fintype.sum_equiv E
  intro σ
  change (if ∀ x ∈ insert v S, σ x = Function.update τ v a x then
      ∏ e ∈ G.edgeFinset, pottsEdgeWeight (pottsReplaceRows W (G.incidenceFinset v) a b) hW' σ e else 0) =
    (if ∀ x ∈ insert v S, T σ x = Function.update τ v b x then
      ∏ e ∈ G.edgeFinset, pottsEdgeWeight W hW (T σ) e else 0)
  by_cases h : ∀ x ∈ insert v S, σ x = Function.update τ v a x
  · rw [if_pos h,if_pos ((hpred σ).1 h)]
    have hσv : σ v = a := by simpa using h v (Finset.mem_insert_self _ _)
    apply Finset.prod_congr rfl
    intro e he
    exact hweight σ hσv e he
  · rw [if_neg h,if_neg (fun h' => h ((hpred σ).2 h'))]
