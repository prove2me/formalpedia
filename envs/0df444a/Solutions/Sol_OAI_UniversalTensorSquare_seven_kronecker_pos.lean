-- Prove2me | solution 1 for OAI.UniversalTensorSquare.seven_kronecker_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:52:39.906214+00:00
-- url     : https://prove2.me/submissions/5028b8ae-4d3c-4cce-b079-0b2191efca09

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_Saxl_kronecker_pos_of_contraction
import Theorems.Thm_OAI_UniversalTensorSquare_eq_diagramOfCols
import Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_transpose
import Theorems.Thm_OAI_UniversalTensorSquare_rowLens_mem_partitionLists

section
-- module Solutions.OAIQ259_US.Saxl_PathAlternation
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl

lemma altWord_fiber_relabel {n m d : ℕ} {α : Type uAlpha}
    (e : Fin n ≃ Fin m) (c : Fin m → α) (a : Fin m → Fin d) (w : Fin n → Fin d) :
    altWord (fiberGroup c) a (w ∘ e.symm) =
      altWord (fiberGroup (c ∘ e)) (a ∘ e) w := by
  classical
  let := Fintype.ofFinite (fiberGroup c)
  let := Fintype.ofFinite (fiberGroup (c ∘ e))
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  apply Fintype.sum_equiv (fiberRelabel e c)
  intro g
  have hs : signC ((fiberRelabel e c g).val) = signC g.val := by
    change signC (e.permCongr g.val) = _
    simp only [signC_def, Equiv.Perm.sign_permCongr]
  rw [hs]
  congr 1
  change (Pi.single (a ∘ e) (1:ℂ) : WordSpace n d) (w ∘ g.val) =
    (Pi.single a (1:ℂ) : WordSpace m d) ((w ∘ e.symm) ∘ (e.permCongr g.val))
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    simpa [Equiv.permCongr] using congrFun h j
  · intro h
    funext i
    simpa [Equiv.permCongr] using congrFun h (e i)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_ColumnContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/

lemma columnPerm_sign (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    signC (columnPerm μ π).val = sg π := by
  change (((Equiv.Perm.sign ((enumerate μ.transpose.rowLens).symm.permCongr (perm π)) : ℤ) : ℂ)) = sg π
  rw [Equiv.Perm.sign_permCongr]
  exact sign_perm π

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_ColumnCertificates
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Certificates. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma polytabloid_reindex {n m : ℕ} {μ : YoungDiagram} (t : Tableau m μ)
    (e : Fin n ≃ Fin m) (w : Fin n → Fin (μ.colLen 0)) :
    polytabloid (e.trans t) w = polytabloid t (w ∘ e.symm) := by
  rw [polytabloid_eq_altWord, polytabloid_eq_altWord]
  exact (altWord_fiber_relabel e (fun i => (t i).val.2) (rowWord t) w).symm

namespace Columns

lemma polytabloid_column_expansion (μ : YoungDiagram) :
    polytabloid (columnTableau μ) =
      ∑ π : Perms μ.transpose.rowLens, sg π • Pi.single (signedRowWord μ π) 1 := by
  classical
  let := Fintype.ofFinite (columnGroup (columnTableau μ))
  rw [polytabloid_eq_altWord, altWord_inverse_sum]
  symm
  apply Fintype.sum_equiv (columnEquiv μ)
  intro π
  rw [← columnPerm_sign μ π]
  congr 2
  funext q
  apply Fin.ext
  change row (perm π (enumerate μ.transpose.rowLens q)) =
    ((columnTableau μ) ((columnEquiv μ π).val q)).val.1
  rw [columnTableau_val]
  simp only [columnEquiv, Equiv.ofBijective_apply, columnPerm, Equiv.permCongr_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply]

lemma polytabloid_placed_expansion {n : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin μ.transpose.rowLens.sum) :
    polytabloid (e.trans (columnTableau μ)) =
      ∑ π : Perms μ.transpose.rowLens, sg π • Pi.single (signedRowWord μ π ∘ e) 1 := by
  classical
  funext w
  rw [polytabloid_reindex, polytabloid_column_expansion]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro π hπ
  congr 1
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro hw
    funext q
    have h := congrFun hw (e q)
    simpa using h
  · intro hw
    funext q
    have h := congrFun hw (e.symm q)
    simpa using h

lemma sgInteger_cast {rs : List ℕ} (π : Perms rs) : (sgInteger π : ℂ) = sg π := by
  induction rs with
  | nil => simp [sgInteger, sg]
  | cons r rs ih => simp only [sgInteger, sg, Int.cast_mul, ih]

lemma contractionInteger_correct {n : ℕ} (α β μ : YoungDiagram)
    (rsA rsB rsT : List ℕ) (ha : α.transpose.rowLens = rsA)
    (hb : β.transpose.rowLens = rsB) (ht : μ.transpose.rowLens = rsT)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (L : ℕ → ℕ → ℕ → ℤ) :
    dotProduct (wordMap (pairFlag L) (polytabloid (tableFor μ rsT ht et)))
      (wordTensor _ _ _ (polytabloid (tableFor α rsA ha ea) ⊗ₜ[ℂ]
        polytabloid (tableFor β rsB hb eb))) =
      (contractionInteger rsA rsB rsT ea eb et L : ℂ) := by
  subst rsA rsB rsT
  simp only [tableFor, polytabloid_placed_expansion, map_sum, map_smul,
    sum_dotProduct, smul_dotProduct]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    TensorProduct.smul_tmul_smul, map_sum, map_smul, wordTensor_single,
    dotProduct_sum, dotProduct_smul, smul_eq_mul,
    dotProduct_single_one, wordMap_single,
    contractionInteger, Int.cast_sum, Int.cast_mul, Int.cast_prod, sgInteger_cast]
  apply Finset.sum_congr rfl
  intro π hπ
  conv_lhs => arg 2; rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro τ hτ
  simp only [mul_assoc]
  congr 3
  apply Finset.prod_congr rfl
  intro q hq
  simp only [pairFlag, mergeWords, Equiv.symm_apply_apply, signedRowWord, Function.comp_apply]

theorem kronecker_pos_of_integer_certificate {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ)
    (rsA rsB rsT : List ℕ) (ha : α.transpose.rowLens = rsA)
    (hb : β.transpose.rowLens = rsB) (ht : μ.transpose.rowLens = rsT)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (L : ℕ → ℕ → ℕ → ℤ) (hcert : contractionInteger rsA rsB rsT ea eb et L ≠ 0) :
    0 < kronecker a b t := by
  apply kronecker_pos_of_contraction a (tableFor α rsA ha ea)
    b (tableFor β rsB hb eb) t (tableFor μ rsT ht et) (pairFlag L)
  rw [contractionInteger_correct]
  exact_mod_cast hcert

end Columns
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FiniteDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Diagrams. -/

section

namespace UniversalTensorSquare

lemma diagramOfCols_cols (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) : (diagramOfCols rs hs).transpose.rowLens = rs := by
  simp only [diagramOfCols, YoungDiagram.transpose_transpose]
  exact YoungDiagram.rowLens_ofRowLens_eq_self hp

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_DomainContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain Contractions. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma Domains.full_weight {rs : List ℕ} (σ : Perms rs) :
    (full rs).weight σ = sgInteger σ := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [full, weight, sgInteger, Finset.mem_univ, ite_true, if_true, ih]

lemma Domains.atValue_weight {rs : List ℕ} (D : Domains rs) (c : Cells rs)
    (j : ℕ) (σ : Perms rs) :
    (D.atValue c j).weight σ = D.weight σ *
      (if row (perm σ c) = j then 1 else 0) := by
  induction rs with
  | nil => exact c.elim
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    rcases σ with ⟨π,σ⟩
    cases c with
    | inl i =>
      simp only [atValue, weight, Finset.mem_filter, perm, Equiv.sumCongr_apply,
        Sum.map_inl, row]
      split_ifs <;> simp_all
    | inr c =>
      simp only [atValue, weight, perm, Equiv.sumCongr_apply, Sum.map_inr, row, ih,
        mul_assoc]

lemma Domains.weight_eq_zero {rs : List ℕ} (D : Domains rs)
    (h : D.vanished = true) (σ : Perms rs) : D.weight σ = 0 := by
  induction rs with
  | nil => simp [vanished] at h
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    rcases σ with ⟨π,σ⟩
    simp only [vanished, Bool.or_eq_true] at h
    rcases h with h | h
    · have hs : s = ∅ := of_decide_eq_true h
      simp [weight, hs]
    · simp only [weight, ih D h σ, mul_zero]

lemma Domains.mass_eq_sum {rs : List ℕ} (D : Domains rs) :
    D.mass = ∑ σ : Perms rs, D.weight σ := by
  classical
  induction rs with
  | nil => simp [mass, weight, Perms]
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [Perms, Fintype.sum_prod_type, weight, ← Finset.mul_sum, ← ih,
      ← Finset.sum_mul, mass]
    congr 1
    simp

lemma domainContraction_nil {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F [] flag = D.mass * E.mass * F.mass := by
  simp only [domainContraction, List.map_nil, List.prod_nil, mul_one,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Domains.mass_eq_sum]

lemma domainContraction_zero {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ))
    (h : (D.vanished || E.vanished || F.vanished) = true) :
    domainContraction D E F edges flag = 0 := by
  rw [domainContraction]
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · simp only [Domains.weight_eq_zero D h, zero_mul, Finset.sum_const_zero]
  · simp only [Domains.weight_eq_zero E h, mul_zero, zero_mul, Finset.sum_const_zero]
  · simp only [Domains.weight_eq_zero F h, mul_zero, zero_mul, Finset.sum_const_zero]

lemma triple_indicator_sum (flag : Finset (ℕ × ℕ × ℕ)) (a b c : ℕ) :
    (∑ v ∈ flag, (if a = v.1 then (1 : ℤ) else 0) *
      (if b = v.2.1 then 1 else 0) * (if c = v.2.2 then 1 else 0)) =
      if (a,b,c) ∈ flag then 1 else 0 := by
  have hh : ∀ v : ℕ × ℕ × ℕ, (if a = v.1 then (1 : ℤ) else 0) *
      (if b = v.2.1 then 1 else 0) * (if c = v.2.2 then 1 else 0) =
      if (a,b,c) = v then 1 else 0 := by
    rintro ⟨x,y,z⟩
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  simp only [hh]
  rw [Finset.sum_ite_eq]

lemma domainContraction_cons {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (c : Edge rsT rsA rsB) (edges : List (Edge rsT rsA rsB))
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F (c::edges) flag =
      ∑ v ∈ flag, domainContraction (D.atValue c.1 v.1)
        (E.atValue c.2.1 v.2.1) (F.atValue c.2.2 v.2.2) edges flag := by
  classical
  simp only [domainContraction, List.map_cons, List.prod_cons, Domains.atValue_weight]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  trans (D.weight π * E.weight σ * F.weight τ) *
    (∑ v ∈ flag, (if row (perm π c.1) = v.1 then (1 : ℤ) else 0) *
      (if row (perm σ c.2.1) = v.2.1 then 1 else 0) *
      (if row (perm τ c.2.2) = v.2.2 then 1 else 0)) *
    (edges.map (fun e => if (row (perm π e.1), row (perm σ e.2.1),
      row (perm τ e.2.2)) ∈ flag then (1 : ℤ) else 0)).prod
  · rw [triple_indicator_sum]
    ring
  · simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    ring

lemma domainContraction_perm {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    {cs es : List (Edge rsT rsA rsB)} (hp : cs.Perm es)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F cs flag = domainContraction D E F es flag := by
  simp only [domainContraction]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  exact congrArg (_ * ·) ((hp.map _).prod_eq)

end Saxl.Columns
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_DomainSolver
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain Solver. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma domainContraction_cons_options {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (c : Edge rsT rsA rsB) (edges : List (Edge rsT rsA rsB))
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F (c::edges) flag =
      ∑ v ∈ edgeOptions D E F c flag, domainContraction (D.atValue c.1 v.1)
        (E.atValue c.2.1 v.2.1) (F.atValue c.2.2 v.2.2) edges flag := by
  rw [domainContraction_cons, edgeOptions, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs with h
  · rfl
  · apply domainContraction_zero
    simpa only [Bool.or_eq_true, Bool.not_eq_false, not_and_or, or_assoc] using h

lemma bringBest_perm {α : Type*} (score : α → ℕ) (cs : List α) :
    (bringBest score cs).Perm cs := by
  induction cs with
  | nil => exact List.Perm.refl _
  | cons c cs ih =>
    rw [bringBest]
    cases he : bringBest score cs with
    | nil =>
      rw [he] at ih
      exact List.Perm.cons c ih
    | cons d ds =>
      rw [he] at ih
      simp only
      split_ifs
      · exact List.Perm.cons c ih
      · exact (List.Perm.swap _ _ _).trans (List.Perm.cons c ih)

lemma orderEdges_perm {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    (orderEdges D E F edges flag).Perm edges := bringBest_perm _ _

theorem solveDomains_correct {rsT rsA rsB : List ℕ} (fuel : ℕ)
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ))
    (h : edges.length ≤ fuel) :
    solveDomains fuel D E F edges flag = domainContraction D E F edges flag := by
  induction fuel generalizing D E F edges with
  | zero =>
    have hh : orderEdges D E F edges flag = [] := by
      apply List.length_eq_zero_iff.mp
      rw [(orderEdges_perm D E F edges flag).length_eq]
      omega
    rw [solveDomains]
    split_ifs with hv
    · exact (domainContraction_zero D E F edges flag hv).symm
    · rw [hh]
      rw [← domainContraction_perm D E F (orderEdges_perm D E F edges flag) flag, hh]
      exact (domainContraction_nil D E F flag).symm
  | succ fuel ih =>
    rw [solveDomains]
    split_ifs with hv
    · exact (domainContraction_zero D E F edges flag hv).symm
    · have hp := orderEdges_perm D E F edges flag
      rw [← domainContraction_perm D E F hp flag]
      cases he : orderEdges D E F edges flag with
      | nil => exact (domainContraction_nil D E F flag).symm
      | cons c cs =>
        have hlen : cs.length ≤ fuel := by
          have hl := hp.length_eq
          rw [he, List.length_cons] at hl
          omega
        rw [domainContraction_cons_options]
        apply Finset.sum_congr rfl
        intro v hv
        exact ih _ _ _ _ hlen

lemma contractionInteger_domains {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      domainContraction (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  simp only [contractionInteger, domainContraction, Domains.full_weight,
    certificateEdges, List.map_ofFn, List.prod_ofFn, Function.comp_apply]

theorem contractionInteger_solve {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      solveDomains n (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  rw [solveDomains_correct n _ _ _ _ _ (by simp [certificateEdges])]
  exact contractionInteger_domains ..

end Saxl.Columns
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_VectorDomainsCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vector Domains Core. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma permVector_get {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (permVector π)[i.val]?.getD 0 = (π i).val := by
  simp [permVector,i.isLt]

lemma sign_eq_aux {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign π = Equiv.Perm.signAux π := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => simp [Equiv.Perm.signAux_one]
  | swap_mul π i j hij ih =>
    rw [Equiv.Perm.sign_mul,Equiv.Perm.signAux_mul,ih,
      Equiv.Perm.sign_swap hij,Equiv.Perm.signAux_swap hij]

lemma vectorSign_perm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    vectorSign n (permVector π) = (Equiv.Perm.sign π : ℤ) := by
  rw [sign_eq_aux]
  simp only [vectorSign,Equiv.Perm.signAux,Units.coe_prod,permVector_get]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [Fin.le_def]
  split_ifs <;> rfl

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_CompactDomainsCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Domains Core. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma CompactDomain.mem_describe {n : ℕ} (π σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    σ ∈ CompactDomain.describe (some (π,s)) ↔ ∀ i, i ∉ s → σ i = π i := by
  simp [describe]

lemma CompactDomain.describe_full (n : ℕ) : (full n).describe = Finset.univ := by
  ext σ; simp [full,mem_describe]

lemma CompactDomain.describe_atValue {n : ℕ} (D : CompactDomain n) (i : Fin n) (j : ℕ) :
    (D.atValue i j).describe = D.describe.filter (fun σ => (σ i).val = j) := by
  cases D with
  | none => simp [atValue,describe]
  | some ds =>
    rcases ds with ⟨π,s⟩
    ext σ
    simp only [Finset.mem_filter,mem_describe]
    by_cases hj : j < n
    · let k := π.symm ⟨j,hj⟩
      have hk : π k = ⟨j,hj⟩ := π.apply_symm_apply _
      by_cases hi : i ∈ s
      · by_cases hks : k ∈ s
        · simp only [atValue,dite_eq_left hj,ite_eq_left hi,show π.symm ⟨j,hj⟩ ∈ s from hks,
            ite_true, if_true,mem_describe]
          constructor
          · intro h
            constructor
            · intro x hx
              have hxi : x ≠ i := by intro he; subst x; exact hx hi
              have hxk : x ≠ π.symm ⟨j,hj⟩ := by intro he; subst x; exact hx hks
              simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hxi hxk] using
                h x (by simp [hx])
            · have hh := h i (by simp)
              simpa [Equiv.Perm.mul_apply,k] using congrArg Fin.val hh
          · rintro ⟨h,hv⟩ x hx
            by_cases hxi : x = i
            · subst x
              simpa [Equiv.Perm.mul_apply,k] using (Fin.ext hv : σ i = ⟨j,hj⟩)
            · have hxs : x ∉ s := by simpa [Finset.mem_erase,hxi] using hx
              have hxk : x ≠ π.symm ⟨j,hj⟩ := by intro he; subst x; exact hxs hks
              simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hxi hxk] using h x hxs
        · simp only [atValue,dite_eq_left hj,ite_eq_left hi,show π.symm ⟨j,hj⟩ ∉ s from hks,
            ite_false, if_false,describe,Finset.notMem_empty,false_iff,not_and]
          intro h hv
          have hki : k = i := σ.injective ((h k hks).trans (hk.trans (Fin.ext hv).symm))
          exact hks (hki.symm ▸ hi)
      · by_cases hv : (π i).val = j
        · simp only [atValue,dite_eq_left hj,ite_eq_right hi,ite_eq_left hv,mem_describe]
          exact ⟨fun h => ⟨h,(congrArg Fin.val (h i hi)).trans hv⟩,fun h => h.1⟩
        · simp only [atValue,dite_eq_left hj,ite_eq_right hi,ite_eq_right hv,describe,Finset.notMem_empty,
            false_iff,not_and]
          intro h he
          exact hv ((congrArg Fin.val (h i hi)).symm.trans he)
    · simp only [atValue,dite_eq_right hj,describe,Finset.notMem_empty,false_iff,not_and]
      intro h hv
      exact hj (hv ▸ (σ i).isLt)

lemma CompactDomain.describe_vanished {n : ℕ} (D : CompactDomain n) :
    decide (D.describe = ∅) = D.vanished := by
  cases D with
  | none => rfl
  | some ds =>
    rcases ds with ⟨π,s⟩
    have hh : π ∈ CompactDomain.describe (some (π,s)) := by simp only [mem_describe]; tauto
    have hn := Finset.ne_empty_of_mem hh
    simp only [hn,decide_false,vanished,Option.isNone_some]

lemma compact_sum_sign {n : ℕ} (π : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    (∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign σ : ℤ)) =
      if s.card ≤ 1 then (Equiv.Perm.sign π : ℤ) else 0 := by
  by_cases hs : s.card ≤ 1
  · rw [ite_eq_left hs]
    have he : CompactDomain.describe (some (π,s)) = {π} := by
      ext σ
      rw [CompactDomain.mem_describe,Finset.mem_singleton]
      constructor
      · intro h
        apply Equiv.ext
        intro i
        by_cases hi : i ∈ s
        · let k := π.symm (σ i)
          have hk : π k = σ i := π.apply_symm_apply _
          by_cases hks : k ∈ s
          · have hki : k = i := Finset.card_le_one.mp hs k hks i hi
            exact (hki ▸ hk).symm
          · have hki : k = i := σ.injective ((h k hks).trans hk)
            exact (hki ▸ hk).symm
        · exact h i hi
      · rintro rfl i hi; rfl
    simp only [he,Finset.sum_singleton]
  · rw [ite_eq_right hs]
    obtain ⟨i,hi,k,hk,hik⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
    let τ := Equiv.swap i k
    have ht : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap hik
    have hm (σ : Equiv.Perm (Fin n)) :
        σ * τ ∈ CompactDomain.describe (some (π,s)) ↔
        σ ∈ CompactDomain.describe (some (π,s)) := by
      simp only [CompactDomain.mem_describe]
      have hh (x : Fin n) (hx : x ∉ s) : τ x = x := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro he; subst x; exact hx hi
        · intro he; subst x; exact hx hk
      simp only [Equiv.Perm.mul_apply]
      constructor <;> intro h x hx <;> simpa only [hh x hx] using h x hx
    have he : (∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign σ : ℤ)) =
        ∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign (σ * τ) : ℤ) := by
      apply Finset.sum_bij (fun σ _ => σ * τ)
      · intro σ hσ; exact (hm σ).mpr hσ
      · intro σ hσ ρ hρ h; exact mul_right_cancel h
      · intro σ hσ
        refine ⟨σ * τ,(hm σ).mpr hσ,?_⟩
        simp [τ,mul_assoc]
      · intro σ hσ
        simp [τ,mul_assoc]
    have hn : (∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign (σ * τ) : ℤ)) =
        -(∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign σ : ℤ)) := by
      simp only [Equiv.Perm.sign_mul,ht,Units.val_neg,mul_neg_one,
        Finset.sum_neg_distrib]
    omega

lemma CompactDomain.describe_mass {n : ℕ} (D : CompactDomain n) :
    (∑ σ ∈ D.describe, (Equiv.Perm.sign σ : ℤ)) = D.mass := by
  cases D with
  | none => simp [describe,mass]
  | some ds =>
    rcases ds with ⟨π,s⟩
    simp only [mass,vectorSign_perm,compact_sum_sign]

lemma CompactDomains.describe_full (rs : List ℕ) : (full rs).describe = Domains.full rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [full,describe,Domains.full,CompactDomain.describe_full,ih]; rfl

lemma CompactDomains.describe_atValue {rs : List ℕ} (D : CompactDomains rs) (c : Cells rs) (j : ℕ) :
    (D.atValue c j).describe = D.describe.atValue c j := by
  induction rs with
  | nil => exact c.elim
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    cases c with
    | inl i => simp only [atValue,describe,Domains.atValue,CompactDomain.describe_atValue]; rfl
    | inr c => simp only [atValue,describe,Domains.atValue,ih]; rfl

lemma CompactDomains.describe_vanished {rs : List ℕ} (D : CompactDomains rs) :
    D.describe.vanished = D.vanished := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [describe,Domains.vanished,vanished,CompactDomain.describe_vanished,ih]

lemma CompactDomains.describe_mass {rs : List ℕ} (D : CompactDomains rs) :
    D.describe.mass = D.mass := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [describe,Domains.mass,mass,CompactDomain.describe_mass,ih]

lemma compactEdgeOptions_describe {rsT rsA rsB : List ℕ}
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (c : Edge rsT rsA rsB) (flag : Finset (ℕ × ℕ × ℕ)) :
    edgeOptions D.describe E.describe F.describe c flag = compactEdgeOptions D E F c flag := by
  simp only [compactEdgeOptions,edgeOptions,← CompactDomains.describe_atValue,
    CompactDomains.describe_vanished]

lemma compactOrderEdges_describe {rsT rsA rsB : List ℕ}
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    orderEdges D.describe E.describe F.describe edges flag = compactOrderEdges D E F edges flag := by
  simp only [compactOrderEdges,orderEdges,compactEdgeOptions_describe]

lemma solveCompact_describe {rsT rsA rsB : List ℕ} (fuel : ℕ)
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    solveDomains fuel D.describe E.describe F.describe edges flag = solveCompact fuel D E F edges flag := by
  induction fuel generalizing D E F edges with
  | zero =>
    rw [solveCompact,solveDomains]
    simp only [CompactDomains.describe_vanished,compactOrderEdges_describe,CompactDomains.describe_mass]
    all_goals (split <;> rfl)
  | succ fuel ih =>
    rw [solveCompact,solveDomains]
    simp only [CompactDomains.describe_vanished,compactOrderEdges_describe,CompactDomains.describe_mass]
    split
    · rfl
    · cases he : compactOrderEdges D E F edges flag with
      | nil => rfl
      | cons c cs =>
        simp only [compactEdgeOptions_describe,← CompactDomains.describe_atValue,ih]

lemma contractionInteger_compact {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      solveCompact n (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  rw [contractionInteger_solve,← CompactDomains.describe_full,← CompactDomains.describe_full,
    ← CompactDomains.describe_full,solveCompact_describe]

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeSeven
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Seven. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

lemma sevenWitness_cols : sevenWitness.transpose.rowLens = [4,1,1,1] :=
  diagramOfCols_cols _ _ (by simp)

lemma sevenWitness_self : sevenWitness.transpose = sevenWitness := by
  apply YoungDiagram.ext
  decide

lemma sevenCertificate0 : contractionInteger [4,1,1,1] [4,1,1,1] [1,1,1,1,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB0 sevenPlaceT0 sevenFlag0 = -6 := by
  unfold sevenFlag0
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate1 : contractionInteger [4,1,1,1] [4,1,1,1] [2,1,1,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB1 sevenPlaceT1 sevenFlag1 = -2 := by
  unfold sevenFlag1
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate2 : contractionInteger [4,1,1,1] [4,1,1,1] [2,2,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB2 sevenPlaceT2 sevenFlag2 = 2 := by
  unfold sevenFlag2
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate3 : contractionInteger [4,1,1,1] [4,1,1,1] [3,1,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB3 sevenPlaceT3 sevenFlag3 = -10 := by
  unfold sevenFlag3
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate4 : contractionInteger [4,1,1,1] [4,1,1,1] [2,2,2,1]
    (Equiv.refl (Fin 7)) sevenPlaceB4 sevenPlaceT4 sevenFlag4 = 2 := by
  unfold sevenFlag4
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate5 : contractionInteger [4,1,1,1] [4,1,1,1] [3,2,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB5 sevenPlaceT5 sevenFlag5 = -2 := by
  unfold sevenFlag5
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate6 : contractionInteger [4,1,1,1] [4,1,1,1] [4,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB6 sevenPlaceT6 sevenFlag6 = 2 := by
  unfold sevenFlag6
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate7 : contractionInteger [4,1,1,1] [4,1,1,1] [3,2,2]
    (Equiv.refl (Fin 7)) sevenPlaceB7 sevenPlaceT7 sevenFlag7 = 2 := by
  unfold sevenFlag7
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

noncomputable section

lemma seven_positive_certificate (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) (hn : rs.sum = 7)
    (eb : Equiv.Perm (Fin 7)) (et : Fin 7 ≃ Fin rs.sum)
    (L : ℕ → ℕ → ℕ → ℤ)
    (hc : contractionInteger [4,1,1,1] [4,1,1,1] rs (Equiv.refl _) eb et L ≠ 0) :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols rs hs) ((diagramOfCols_card rs hs hp).trans hn)) := by
  exact kronecker_pos_of_integer_certificate _ _ _ [4,1,1,1] [4,1,1,1] rs
    sevenWitness_cols sevenWitness_cols (diagramOfCols_cols _ _ hp)
    (Equiv.refl _) eb et L hc

lemma seven_positive0 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [1,1,1,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [1,1,1,1,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB0 sevenPlaceT0 sevenFlag0
  intro hz
  have hh : (-6 : ℤ) = 0 := sevenCertificate0.symm.trans hz
  norm_num at hh

lemma seven_positive1 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [2,1,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [2,1,1,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB1 sevenPlaceT1 sevenFlag1
  intro hz
  have hh : (-2 : ℤ) = 0 := sevenCertificate1.symm.trans hz
  norm_num at hh

lemma seven_positive2 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [2,2,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [2,2,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB2 sevenPlaceT2 sevenFlag2
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate2.symm.trans hz
  norm_num at hh

lemma seven_positive3 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [3,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [3,1,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB3 sevenPlaceT3 sevenFlag3
  intro hz
  have hh : (-10 : ℤ) = 0 := sevenCertificate3.symm.trans hz
  norm_num at hh

lemma seven_positive4 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [2,2,2,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [2,2,2,1] (by decide) (by simp) rfl
    sevenPlaceB4 sevenPlaceT4 sevenFlag4
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate4.symm.trans hz
  norm_num at hh

lemma seven_positive5 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [3,2,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [3,2,1,1] (by decide) (by simp) rfl
    sevenPlaceB5 sevenPlaceT5 sevenFlag5
  intro hz
  have hh : (-2 : ℤ) = 0 := sevenCertificate5.symm.trans hz
  norm_num at hh

lemma seven_positive6 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [4,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [4,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB6 sevenPlaceT6 sevenFlag6
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate6.symm.trans hz
  norm_num at hh

lemma seven_positive7 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [3,2,2] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [3,2,2] (by decide) (by simp) rfl
    sevenPlaceB7 sevenPlaceT7 sevenFlag7
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate7.symm.trans hz
  norm_num at hh

lemma seven_positive_target_eq {μ ν : YoungDiagram} (hμ : μ.card = 7) (hν : ν.card = 7)
    (he : μ = ν)
    (hp : 0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card) (canonicalTableau ν hν)) :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card) (canonicalTableau μ hμ) := by
  subst ν
  exact hp

lemma partitionLists_seven : partitionLists 7 7 7 =
    {[7],[6,1],[5,2],[5,1,1],[4,3],[4,2,1],[4,1,1,1],[3,3,1],[3,2,2],[3,2,1,1],[3,1,1,1,1],[2,2,2,1],[2,2,1,1,1],[2,1,1,1,1,1],[1,1,1,1,1,1,1]} := by decide

theorem seven_kronecker_pos_oai (ν : YoungDiagram) (hν : ν.card = 7) :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card) (canonicalTableau ν hν) := by
  have hc := rowLens_mem_partitionLists ν.transpose
  rw [transpose_card, hν, partitionLists_seven] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have he := eq_diagramOfCols ν [7] (by decide) h
    have ht : diagramOfCols [7] (by decide) =
        (diagramOfCols [1,1,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive0
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [6,1] (by decide) h
    have ht : diagramOfCols [6,1] (by decide) =
        (diagramOfCols [2,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive1
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,2] (by decide) h
    have ht : diagramOfCols [5,2] (by decide) =
        (diagramOfCols [2,2,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive2
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,1,1] (by decide) h
    have ht : diagramOfCols [5,1,1] (by decide) =
        (diagramOfCols [3,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive3
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,3] (by decide) h
    have ht : diagramOfCols [4,3] (by decide) =
        (diagramOfCols [2,2,2,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive4
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,2,1] (by decide) h
    have ht : diagramOfCols [4,2,1] (by decide) =
        (diagramOfCols [3,2,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive5
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,1,1,1] (by decide) h
    subst ν
    exact seven_positive6
  · have he := eq_diagramOfCols ν [3,3,1] (by decide) h
    have ht : diagramOfCols [3,3,1] (by decide) =
        (diagramOfCols [3,2,2] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive7
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [3,2,2] (by decide) h
    subst ν
    exact seven_positive7
  · have he := eq_diagramOfCols ν [3,2,1,1] (by decide) h
    subst ν
    exact seven_positive5
  · have he := eq_diagramOfCols ν [3,1,1,1,1] (by decide) h
    subst ν
    exact seven_positive3
  · have he := eq_diagramOfCols ν [2,2,2,1] (by decide) h
    subst ν
    exact seven_positive4
  · have he := eq_diagramOfCols ν [2,2,1,1,1] (by decide) h
    subst ν
    exact seven_positive2
  · have he := eq_diagramOfCols ν [2,1,1,1,1,1] (by decide) h
    subst ν
    exact seven_positive1
  · have he := eq_diagramOfCols ν [1,1,1,1,1,1,1] (by decide) h
    subst ν
    exact seven_positive0

universe u

end
end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.seven_kronecker_pos_oai := @OAI.UniversalTensorSquare.seven_kronecker_pos_oai
