-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.upperUnipotent_edge_fixed_iff_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:04:20.905045+00:00
-- url     : https://prove2.me/submissions/57d970c9-5b22-403d-8a16-06156ad835c4

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_right_mul_eq_self_iff
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsGenerators401_ne_conj_upperUnipotent


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGraph
open Matrix
open LPSArithmetic LPSGenerators
namespace QEC.Coding.BalancedProduct.LPSGraph
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {g w : PGL(2, ZMod q)}
    (hgw : (lpsCayleyGraph401 q hq).Adj g w)
    (h : upperUnipotentSubgroup (R := ZMod q)) :
    s(g * (h : PGL(2, ZMod q)), w * (h : PGL(2, ZMod q))) = s(g, w) ↔
      h = 1 := by
  constructor
  · intro hedge
    rw [Sym2.eq_iff] at hedge
    rcases hedge with ⟨hg, _⟩ | ⟨hgwSwap, _⟩
    · exact (right_mul_eq_self_iff g h).mp hg
    · rcases (lpsCayleyGraph401_adj_iff q hq g w).mp hgw with
        ⟨s, hs, hsg⟩
      rcases (mem_upperUnipotentSubgroup_iff
        (R := ZMod q) (h : PGL(2, ZMod q))).mp h.property with ⟨x, hx⟩
      have hconj : s = g * upperUnipotentPGL x * g⁻¹ := by
        rw [hx]
        apply mul_right_cancel (b := g)
        calc
          s * g = w := hsg
          _ = g * (h : PGL(2, ZMod q)) := hgwSwap.symm
          _ = (g * (h : PGL(2, ZMod q)) * g⁻¹) * g := by simp [mul_assoc]
      exact (lpsGenerators401_ne_conj_upperUnipotent q hq hs g x hconj).elim
  · rintro rfl
    simp
end QEC.Coding.BalancedProduct.LPSGraph
