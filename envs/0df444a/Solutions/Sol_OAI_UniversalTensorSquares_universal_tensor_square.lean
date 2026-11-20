-- Prove2me | solution 1 for OAI.UniversalTensorSquares.universal_tensor_square
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:07:36.073028+00:00
-- url     : https://prove2.me/submissions/2aee03a2-585f-4674-aa5f-5bcfd6481e6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_Saxl_Balance_WordPacking_kronecker_pos
import Theorems.Thm_OAI_Saxl_Balance_balancePacking
import Definitions.Def_OAIQ259US000
import Definitions.Def_OAIQ259US001
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Definitions.Def_OAIQ259US006
import Theorems.Thm_OAI_UniversalTensorSquare_band_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_rowLens
import Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_transpose
import Theorems.Thm_OAI_UniversalTensorSquare_universal_partition_exceptional
import Theorems.Thm_OAI_UniversalTensorSquare_universal_partition_le64

section
-- module Solutions.OAIQ259_US.Saxl_Basic
attribute [-instance] _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
theorem intertwining_finrank_pos_iff {G : Type uG} {V : Type uV} {W : Type uW} [Group G]
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    0 < Module.finrank ℂ (Representation.IntertwiningMap ρ σ) ↔
      ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 :=
  Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := Representation.IntertwiningMap ρ σ)

theorem kronecker_pos_iff {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) :
    0 < kronecker a b t ↔
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        ((spechtRep a).tprod (spechtRep b)), f ≠ 0 := by
  exact @intertwining_finrank_pos_iff (Equiv.Perm (Fin n)) (Specht t)
    (Specht a ⊗[ℂ] Specht b) _ _ _ _ _ _ _
    (spechtRep t) ((spechtRep a).tprod (spechtRep b))

/- Column permutations cannot also fix the row word unless they are identity. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_HorizontalRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl


lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  simp [rowPrefix, Finset.sum_range_succ]

lemma rowPrefix_le_card (μ : YoungDiagram) (k : ℕ) : rowPrefix μ k ≤ μ.card := by
  rw [← rowPrefix_eq_card μ (Nat.le_max_left _ k)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_right _ _))

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_DominatedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

lemma colTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (colTruncate μ k).rowLen i = min k (μ.rowLen i) := by
  have hh : ∀ j, j < (colTruncate μ k).rowLen i ↔ j < min k (μ.rowLen i) := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    change (i,j) ∈ (rowTruncate μ.transpose k).transpose ↔ _
    rw [YoungDiagram.mem_transpose]
    change (j,i) ∈ rowTruncate μ.transpose k ↔ _
    rw [mem_rowTruncate, YoungDiagram.mem_transpose]
    simp only [Prod.swap_prod_mk, YoungDiagram.mem_iff_lt_rowLen, lt_min_iff]
    omega
  have h₁ := hh ((colTruncate μ k).rowLen i)
  have h₂ := hh (min k (μ.rowLen i))
  omega

lemma colTruncate_height (μ : YoungDiagram) (k : ℕ) :
    (colTruncate μ k).colLen 0 ≤ μ.colLen 0 := by
  by_contra h
  have hm : (μ.colLen 0,0) ∈ colTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hm
  rw [colTruncate_rowLen, rowLen_zero_of_height_le μ le_rfl] at hr
  simp at hr

lemma sum_range_if_lt (f : ℕ → ℕ) {r H : ℕ} (hr : r ≤ H) :
    (∑ i ∈ Finset.range H, if i < r then f i else 0) = ∑ i ∈ Finset.range r, f i := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma corner_inequality (μ : YoungDiagram) (k r : ℕ) :
    rowPrefix μ.transpose k + rowPrefix μ r ≤ μ.card + r*k := by
  let H := max (μ.colLen 0) r
  have hh : μ.colLen 0 ≤ H := Nat.le_max_left _ _
  have hr : r ≤ H := Nat.le_max_right _ _
  have hm : rowPrefix μ.transpose k = ∑ i ∈ Finset.range H, min k (μ.rowLen i) := by
    rw [← rowTruncate_card, ← transpose_card (rowTruncate μ.transpose k)]
    change (colTruncate μ k).card = _
    rw [← rowPrefix_eq_card _ ((colTruncate_height μ k).trans hh)]
    exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)
  rw [hm, ← rowPrefix_eq_card μ hh]
  change _ + (∑ i ∈ Finset.range r, μ.rowLen i) ≤ (∑ i ∈ Finset.range H, μ.rowLen i) + r*k
  have hconst : (∑ i ∈ Finset.range r, k) = r*k := by simp
  rw [← hconst, ← sum_range_if_lt μ.rowLen hr, ← sum_range_if_lt (fun _ => k) hr,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> omega

lemma corner_equality (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ.transpose k + rowPrefix μ (μ.colLen k) = μ.card + μ.colLen k*k := by
  let r := μ.colLen k
  let H := μ.colLen 0
  have hr : r ≤ H := μ.colLen_anti 0 k (Nat.zero_le _)
  have hm : rowPrefix μ.transpose k = ∑ i ∈ Finset.range H, min k (μ.rowLen i) := by
    rw [← rowTruncate_card, ← transpose_card (rowTruncate μ.transpose k)]
    change (colTruncate μ k).card = _
    rw [← rowPrefix_eq_card _ (colTruncate_height μ k)]
    exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)
  change rowPrefix μ.transpose k + rowPrefix μ r = μ.card + r*k
  rw [hm, ← rowPrefix_eq_card μ (le_refl H)]
  change _ + (∑ i ∈ Finset.range r, μ.rowLen i) = (∑ i ∈ Finset.range H, μ.rowLen i) + r*k
  have hconst : (∑ i ∈ Finset.range r, k) = r*k := by simp
  rw [← hconst, ← sum_range_if_lt μ.rowLen hr, ← sum_range_if_lt (fun _ => k) hr,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have he : i < r ↔ k < μ.rowLen i := by
    exact YoungDiagram.mem_iff_lt_colLen.symm.trans YoungDiagram.mem_iff_lt_rowLen
  split_ifs with h
  · have hh := he.mp h
    omega
  · have hh := not_congr he |>.mp h
    omega

/- Ordinary conjugation reverses dominance, including empty diagrams. -/
theorem dominates_transpose {μ ν : YoungDiagram} (hc : μ.card = ν.card)
    (h : Dominates μ ν) : Dominates ν.transpose μ.transpose := by
  intro k
  have h₁ := corner_inequality μ k (ν.colLen k)
  have h₂ := corner_equality ν k
  have h₃ := h (ν.colLen k)
  omega

open scoped MonoidAlgebra

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ZeroColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero Columns. -/

section

noncomputable section
namespace Saxl.Columns

lemma sum_fin_val_ite (r i : ℕ) :
    (∑ j : Fin r, if j.val = i then (1:ℕ) else 0) = if i < r then 1 else 0 := by
  classical
  by_cases hi : i < r
  · rw [ite_eq_left hi, Finset.sum_eq_single (⟨i,hi⟩ : Fin r)]
    · simp
    · intro j hj hji
      exact ite_eq_right (fun h => hji (Fin.ext h))
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun h : (j : ℕ) = i => hi (h ▸ j.isLt))

lemma cells_row_count (rs : List ℕ) (i : ℕ) :
    (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) = rs.countP (fun h => i < h) := by
  classical
  induction rs with
  | nil => simp [Cells]
  | cons h rs ih =>
    rw [show (∑ c : Cells (h :: rs), if row c = i then (1:ℕ) else 0) =
      (∑ c : Fin h, if c.val = i then (1:ℕ) else 0) +
        (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) from
      Fintype.sum_sum_type _]
    rw [sum_fin_val_ite, ih, List.countP_cons]
    split_ifs <;> simp_all <;> omega

lemma placed_rowLen {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (i : ℕ) :
    μ.rowLen i = rs.countP (fun h => i < h) := by
  classical
  let E : {c : Cells rs // row c = i} ≃ {c : μ.cells // c.val.1 = i} :=
    e.subtypeEquiv (fun c => by rw [hr])
  have hc := Fintype.card_congr (E.trans (rowFiberEquiv μ i))
  rw [Fintype.card_fin, Fintype.card_subtype, Finset.card_filter, cells_row_count] at hc
  exact hc.symm

lemma columnShape_rowLen (rs : List ℕ) (i : ℕ) :
    (columnShape rs).rowLen i = rs.countP (fun h => i < h) := by
  obtain ⟨e,hr,_⟩ := columnShape_placement rs
  exact placed_rowLen e hr i

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_Extensions
attribute [-simp] _root_.OAI.UniversalTensorSquare.candidate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extensions. -/

section

noncomputable section
open scoped TensorProduct

namespace UniversalTensorSquare

universe u

theorem irreducibles_of_kronecker_pos {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hpos : ∀ (ν : YoungDiagram) (hν : ν.card = n),
      0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
        (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) :
    Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
      (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
      ∃ F : Representation.IntertwiningMap ρ
        ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
          (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
        Function.Injective F := by
  refine ⟨Saxl.specht_irreducible _, ?_⟩
  intro V _ _ _ ρ _
  obtain ⟨p, ⟨e⟩⟩ := Saxl.irreducible_equiv_specht ρ
  obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp
    (hpos (Saxl.partitionDiagram p) (Saxl.partitionDiagram_card p))
  let := Saxl.specht_irreducible (Saxl.canonicalTableau (Saxl.partitionDiagram p)
    (Saxl.partitionDiagram_card p))
  have hs := Representation.IsIrreducible.injective_or_eq_zero
    (W := Saxl.Specht (Saxl.canonicalTableau lam hlam) ⊗[ℂ]
      Saxl.Specht (Saxl.canonicalTableau lam hlam)) f
  have hi : Function.Injective f := hs.resolve_right hf
  exact ⟨f.comp e.toIntertwiningMap, hi.comp e.injective⟩

lemma remainderPairs_bound_odd (n : ℕ) (hodd : staircaseIndex n % 2 = 1) :
    2 * remainderPairs n ≤ staircaseIndex n - 1 := by
  have hs := staircaseIndex_spec n
  have hd := degree_eq n
  have hpar : (Saxl.staircase (staircaseIndex n + 1)).card % 2 = n % 2 := by
    rw [Saxl.staircase_card_succ]
    omega
  have hlt : n < (Saxl.staircase (staircaseIndex n + 1)).card := by
    by_contra hh
    have := le_staircaseIndex n (staircaseIndex n + 1) (by omega) hpar
    omega
  rw [Saxl.staircase_card_succ] at hlt
  omega

lemma remainderPairs_bound_even (n : ℕ) (heven : staircaseIndex n % 2 = 0) :
    2 * remainderPairs n ≤ 3 * staircaseIndex n + 4 := by
  have hs := staircaseIndex_spec n
  have hd := degree_eq n
  have hsucc : (Saxl.staircase (staircaseIndex n + 3)).card =
      (Saxl.staircase (staircaseIndex n)).card + 3 * staircaseIndex n + 6 := by
    have h1 := Saxl.staircase_card_succ (staircaseIndex n)
    have h2 : (Saxl.staircase (staircaseIndex n + 2)).card =
        (Saxl.staircase (staircaseIndex n + 1)).card + (staircaseIndex n + 2) := by
      simpa [Nat.add_assoc] using Saxl.staircase_card_succ (staircaseIndex n + 1)
    have h3 : (Saxl.staircase (staircaseIndex n + 3)).card =
        (Saxl.staircase (staircaseIndex n + 2)).card + (staircaseIndex n + 3) := by
      simpa [Nat.add_assoc] using Saxl.staircase_card_succ (staircaseIndex n + 2)
    omega
  have hpar : (Saxl.staircase (staircaseIndex n + 3)).card % 2 = n % 2 := by
    rw [hsucc]
    omega
  have hlt : n < (Saxl.staircase (staircaseIndex n + 3)).card := by
    by_contra hh
    have := le_staircaseIndex n (staircaseIndex n + 3) (by omega) hpar
    omega
  rw [hsucc] at hlt
  omega

end UniversalTensorSquare

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

lemma sum_wordContent {n d : ℕ} (w : Fin n → Fin d) :
    ∑ j, wordContent w j = n := by
  classical
  simp only [wordContent,Finset.card_filter]
  rw [Finset.sum_comm]
  simp

namespace Balance
open FlagColumns Columns

lemma WordPacking.total {rs ps : List ℕ} {d : ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {marks : Finset ℕ}
    (P : WordPacking rs ps d A label marks) : ps.sum = rs.sum := by
  calc
    ps.sum = ∑ j, ps.get j := by rw [← List.sum_ofFn, List.ofFn_get]
    _ = ∑ j, wordContent P.word j := Finset.sum_congr rfl (fun j _ => (P.counts j).symm)
    _ = rs.sum := sum_wordContent P.word

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_PartWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Part Words. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

lemma balancedParts_part {n k p : ℕ} (hp : p ∈ balancedParts n k) :
    n/k ≤ p ∧ p ≤ (n+k-1)/k := by
  simp only [balancedParts, List.mem_ofFn] at hp
  obtain ⟨j,rfl⟩ := hp
  have hk : 0 < k := Nat.zero_lt_of_lt j.isLt
  have hn : n = k*(n/k) + n%k := (Nat.div_add_mod n k).symm
  have hr := Nat.mod_lt n hk
  constructor
  · omega
  · split_ifs with h
    · apply (Nat.le_div_iff_mul_le hk).mpr
      have ht : n%k ≥ 1 := by omega
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm]
      omega
    · apply (Nat.le_div_iff_mul_le hk).mpr
      simp only [Nat.add_zero]
      rw [Nat.mul_comm]
      omega

lemma balancedParts_pos {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ∀ p ∈ balancedParts n k, 0 < p := by
  intro p hp
  have h := (balancedParts_part hp).1
  have hn : 1 ≤ n/k := (Nat.le_div_iff_mul_le hk).mpr (by simpa)
  omega

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_Candidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate. -/

section

noncomputable section
namespace UniversalTensorSquare

lemma fixedCandidate_eq_staircase_of_remainder_zero (n : ℕ)
    (hr : remainderPairs n = 0) :
    fixedCandidate n = Saxl.staircase (staircaseIndex n) := by
  simp only [fixedCandidate, hr, Nat.zero_div, Nat.zero_mod, candidate_zero]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_TransposeSupport
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transpose Support. -/

section

noncomputable section
open scoped TensorProduct

namespace UniversalTensorSquare

theorem kronecker_pos_transpose_iff {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n) :
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ↔
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν))) := by
  constructor
  · exact kronecker_pos_transpose lam hlam hself ν hν
  · intro h
    have ht := kronecker_pos_transpose lam hlam hself ν.transpose
      ((Saxl.transpose_card ν).trans hν) h
    obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp ht
    let e := spechtShapeEquiv (YoungDiagram.transpose_transpose ν).symm
      (Saxl.canonicalTableau ν hν)
      (Saxl.canonicalTableau ν.transpose.transpose
        ((Saxl.transpose_card ν.transpose).trans ((Saxl.transpose_card ν).trans hν)))
    apply (Saxl.kronecker_pos_iff _ _ _).mpr
    refine ⟨f.comp e.toIntertwiningMap, ?_⟩
    intro hz
    apply hf
    ext x
    have hh := congrArg (fun F => F (e.symm x)) hz
    change f (e (e.symm x)) = 0 at hh
    simpa using hh

lemma fixedCandidate_support_transpose (n : ℕ) (hM : 3 ≤ staircaseIndex n)
    (ν : YoungDiagram) (hν : ν.card = n) :
    (0 < Saxl.kronecker (Saxl.canonicalTableau (fixedCandidate n) (fixedCandidate_card n hM))
      (Saxl.canonicalTableau (fixedCandidate n) (fixedCandidate_card n hM))
      (Saxl.canonicalTableau ν hν)) ↔
    (0 < Saxl.kronecker (Saxl.canonicalTableau (fixedCandidate n) (fixedCandidate_card n hM))
      (Saxl.canonicalTableau (fixedCandidate n) (fixedCandidate_card n hM))
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν))) :=
  kronecker_pos_transpose_iff _ _ (fixedCandidate_transpose n) ν hν

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Blocks. -/

section

noncomputable section
namespace Saxl.Balance

lemma bigParts_length {q δ : ℕ} (hδ : δ ≤ 1) : (bigParts q δ).length = 5-δ := by
  simp only [bigParts,List.length_append,balancedParts_length,oneIf]
  split_ifs <;> simp_all <;> omega

lemma shortParts_length {m τ : ℕ} (hτ : τ ≤ 1) : (shortParts m τ).length = 1+τ := by
  simp only [shortParts]
  split_ifs <;> simp_all
  omega

lemma oneIf_length {x ε : ℕ} (hε : ε ≤ 1) : (oneIf x ε).length = ε := by
  unfold oneIf
  split_ifs <;> simp_all
  omega

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_PairRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Run. -/

section

noncomputable section
namespace Saxl.Balance

lemma pairColumns_succ (a m : ℕ) :
    pairColumns a (m+1) = pairColumns a m ++ [a+2*m+1,a+2*m] := by
  simp [pairColumns,List.range_succ]

lemma pairParts_succ (a m : ℕ) :
    pairParts a (m+1) = pairParts a m ++ balancedParts (2*(a+2*m)+1) 4 := by
  simp [pairParts,List.range_succ]

lemma pairColumns_perm (a m : ℕ) : (pairColumns a m).Perm (List.range' a (2*m)) := by
  induction m with
  | zero => simp [pairColumns]
  | succ m ih =>
    rw [pairColumns_succ]
    have hpair : [a+2*m+1,a+2*m].Perm (List.range' (a+2*m) 2) := by
      simpa [List.range'] using List.Perm.swap (a+2*m) (a+2*m+1) []
    have h := ih.append hpair
    rw [List.range'_append_1] at h
    simpa only [Nat.mul_add,Nat.mul_one] using h

lemma pairParts_length (a m : ℕ) : (pairParts a m).length = 4*m := by
  induction m with
  | zero => simp [pairParts]
  | succ m ih => rw [pairParts_succ,List.length_append,ih,balancedParts_length]; omega

lemma pairParts_positive {a m : ℕ} (ha : 2 ≤ a) : ∀ p ∈ pairParts a m, 0 < p := by
  intro p hp
  obtain ⟨j,hj,hp⟩ := List.mem_flatMap.mp hp
  exact balancedParts_pos (by decide) (by omega) p hp

lemma pairParts_bound {a m p : ℕ} (_ha : 2 ≤ a) (hp : p ∈ pairParts a m) :
    p < a+2*m := by
  obtain ⟨j,hj,hp⟩ := List.mem_flatMap.mp hp
  have hj := List.mem_range.mp hj
  have hb := (balancedParts_part hp).2
  omega

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Assembly. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

lemma balanceParts_length {M b δ τ ε m : ℕ}
    (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1) (heq : M = 4+τ+ε+2*m) :
    2*M-5 ≤ (balanceParts M b δ τ ε m).length := by
  rw [balanceParts,List.length_append,List.length_append,List.length_append,
    bigParts_length hδ,shortParts_length hτ,pairParts_length,oneIf_length hε]
  omega

lemma oneIf_mem {x ε p : ℕ} (hp : p ∈ oneIf x ε) : p = x := by
  unfold oneIf at hp
  split_ifs at hp
  · simp at hp
  · exact List.mem_singleton.mp hp

lemma balanceParts_positive {M b δ τ ε m : ℕ} (hM : 4 ≤ M) :
    ∀ p ∈ balanceParts M b δ τ ε m, 0 < p := by
  intro p hp
  simp only [balanceParts,List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact balancedParts_pos (by decide) (by omega) p hp
    · have := oneIf_mem hp; omega
  · unfold shortParts at hp
    split_ifs at hp
    · have := List.mem_singleton.mp hp; omega
    · exact balancedParts_pos (by decide) (by omega) p hp
  · exact pairParts_positive (by omega) p hp
  · have := oneIf_mem hp; omega

lemma balanceParts_bound {M b δ τ ε m p : ℕ}
    (hM : 4 ≤ M) (hb : b ≤ M-2) (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1)
    (heq : M = 4+τ+ε+2*m) (hsmall : τ = 0 → 2*(b+1) ≤ M)
    (hp : p ∈ balanceParts M b δ τ ε m) : p ≤ M+1 := by
  simp only [balanceParts,List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · rcases List.mem_append.mp hp with hp | hp
    · have hh := (balancedParts_part hp).2
      omega
    · have := oneIf_mem hp; omega
  · unfold shortParts at hp
    split_ifs at hp with ht
    · have := List.mem_singleton.mp hp
      have := hsmall ht
      omega
    · have hh := (balancedParts_part hp).2
      omega
  · have := pairParts_bound (by omega : 2 ≤ 3+τ+ε) hp
    omega
  · have := oneIf_mem hp; omega

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Capacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capacity. -/

section

noncomputable section

namespace UniversalTensorSquare

open Saxl

lemma colPrefix_eq_sum (μ : YoungDiagram) (i : ℕ) :
    colPrefix μ i = ∑ k ∈ Finset.range i, μ.colLen k := by
  simp only [colPrefix, rowPrefix, YoungDiagram.rowLen_transpose]

lemma mem_colTruncate (μ : YoungDiagram) (i : ℕ) (a b : ℕ) :
    (a,b) ∈ colTruncate μ i ↔ (a,b) ∈ μ ∧ b < i := by
  simp only [colTruncate, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    Saxl.mem_rowTruncate]

lemma rowTruncate_subset (μ : YoungDiagram) (j : ℕ) :
    (rowTruncate μ j).cells ⊆ μ.cells := by
  intro p hp
  exact (Saxl.mem_rowTruncate.mp hp).1

lemma colTruncate_subset (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).cells ⊆ μ.cells := by
  rintro ⟨a,b⟩ hp
  exact ((mem_colTruncate μ i a b).mp hp).1

lemma colTruncate_card (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).card = colPrefix μ i := by
  rw [colTruncate, Saxl.transpose_card, rowTruncate_card, colPrefix]

lemma strip_area_identity (μ : YoungDiagram) (i j : ℕ) :
    μ.card + ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card =
      rowPrefix μ j + colPrefix μ i +
        (μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells)).card := by
  have hu : (rowTruncate μ j).cells ∪ (colTruncate μ i).cells ⊆ μ.cells :=
    Finset.union_subset (rowTruncate_subset μ j) (colTruncate_subset μ i)
  have h₁ := Finset.card_sdiff_add_card_eq_card hu
  have h₂ := Finset.card_union_add_card_inter
    (rowTruncate μ j).cells (colTruncate μ i).cells
  have h₃ := rowTruncate_card μ j
  have h₄ := colTruncate_card μ i
  change (rowTruncate μ j).cells.card = _ at h₃
  change (colTruncate μ i).cells.card = _ at h₄
  change μ.cells.card + _ = _
  omega

lemma corner_subset_rectangle (μ : YoungDiagram) {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells) ⊆
      Finset.Ico j (μ.colLen (i-1)) ×ˢ Finset.Ico i (μ.rowLen (j-1)) := by
  rintro ⟨a,b⟩ hp
  simp only [Finset.mem_sdiff, Finset.mem_union, YoungDiagram.mem_cells,
    mem_rowTruncate, mem_colTruncate, not_or] at hp
  have ha : j ≤ a := Nat.le_of_not_gt fun ha => hp.2.1 ⟨hp.1, ha⟩
  have hb : i ≤ b := Nat.le_of_not_gt fun hb => hp.2.2 ⟨hp.1, hb⟩
  have ha' : a < μ.colLen (i-1) := YoungDiagram.mem_iff_lt_colLen.mp
    (μ.up_left_mem le_rfl (by omega) hp.1)
  have hb' : b < μ.rowLen (j-1) := YoungDiagram.mem_iff_lt_rowLen.mp
    (μ.up_left_mem (by omega) le_rfl hp.1)
  simpa only [Finset.mem_product, Finset.mem_Ico] using And.intro ⟨ha, ha'⟩ ⟨hb,hb'⟩

lemma prefix_last_mul_le (μ : YoungDiagram) {j : ℕ} (hj : 0 < j) :
    j * μ.rowLen (j-1) ≤ rowPrefix μ j := by
  have h := Finset.sum_le_sum (s := Finset.range j) (f := fun _ => μ.rowLen (j-1))
    (g := fun a => μ.rowLen a) (by
      intro a ha
      exact μ.rowLen_anti a (j-1) (by have := Finset.mem_range.mp ha; omega))
  simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, rowPrefix] using h

theorem capacity_rectangle (μ : YoungDiagram) {i j U V : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hU : colPrefix μ i ≤ U) (hV : rowPrefix μ j ≤ V) :
    μ.card ≤ max (U+V-1) (U*V/(i*j)) := by
  classical
  by_cases hcell : (j-1,i-1) ∈ μ
  · have heq : (rowTruncate μ j).cells ∩ (colTruncate μ i).cells =
        (rectangle j i).cells := by
      ext ⟨a,b⟩
      simp only [Finset.mem_inter, YoungDiagram.mem_cells, Saxl.mem_rowTruncate,
        mem_colTruncate, mem_rectangle]
      constructor
      · tauto
      · rintro ⟨ha,hb⟩
        have hx := μ.up_left_mem (by omega : a ≤ j-1) (by omega : b ≤ i-1) hcell
        tauto
    have hint : ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card = j*i := by
      rw [heq]
      simp only [rectangle, Finset.card_product, Finset.card_range]
    have hcorner := Finset.card_le_card (corner_subset_rectangle μ hi hj)
    simp only [Finset.card_product, Nat.card_Ico] at hcorner
    have hid := strip_area_identity μ i j
    rw [hint, Nat.mul_comm j i] at hid
    have harea : μ.card + i*j ≤ U+V + (μ.colLen (i-1)-j)*(μ.rowLen (j-1)-i) := by
      omega
    have hx : j ≤ μ.colLen (i-1) := by
      have := YoungDiagram.mem_iff_lt_colLen.mp hcell
      omega
    have hy : i ≤ μ.rowLen (j-1) := by
      have := YoungDiagram.mem_iff_lt_rowLen.mp hcell
      omega
    have hxu : i*μ.colLen (i-1) ≤ U := by
      simpa only [YoungDiagram.rowLen_transpose] using
        (prefix_last_mul_le μ.transpose hi).trans hU
    have hyv : j*μ.rowLen (j-1) ≤ V := (prefix_last_mul_le μ hj).trans hV
    have hu : i*j ≤ U := (Nat.mul_le_mul_left i hx).trans hxu
    have hv : i*j ≤ V := by nlinarith
    have ha : i*(μ.colLen (i-1)-j) ≤ U-i*j := by
      rw [Nat.mul_sub_left_distrib]
      exact Nat.sub_le_sub_right hxu _
    have hb : j*(μ.rowLen (j-1)-i) ≤ V-i*j := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_comm j i]
      exact Nat.sub_le_sub_right hyv _
    have hprod := Nat.mul_le_mul ha hb
    have hscaled := Nat.mul_le_mul_left (i*j) harea
    have hmul : μ.card * (i*j) ≤ U*V := by
      have hU' := Nat.sub_add_cancel hu
      have hV' := Nat.sub_add_cancel hv
      nlinarith
    exact (Nat.le_div_iff_mul_le (Nat.mul_pos hi hj)).mpr hmul |>.trans (le_max_right _ _)
  · have hcorner : μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨a,b⟩ hp
      simp only [Finset.mem_sdiff, Finset.mem_union, YoungDiagram.mem_cells,
        mem_rowTruncate, mem_colTruncate, not_or] at hp
      have ha : j ≤ a := Nat.le_of_not_gt fun ha => hp.2.1 ⟨hp.1, ha⟩
      have hb : i ≤ b := Nat.le_of_not_gt fun hb => hp.2.2 ⟨hp.1, hb⟩
      exact hcell (μ.up_left_mem (by omega) (by omega) hp.1)
    by_cases hn : μ.card = 0
    · simp [hn]
    have hzero : (0,0) ∈ μ := by
      obtain ⟨⟨a,b⟩,hp⟩ := Finset.card_pos.mp (show 0 < μ.cells.card from Nat.pos_of_ne_zero hn)
      exact μ.up_left_mem (Nat.zero_le _) (Nat.zero_le _) hp
    have hzmem : (0,0) ∈ (rowTruncate μ j).cells ∩ (colTruncate μ i).cells := by
      simpa only [Finset.mem_inter, YoungDiagram.mem_cells, mem_rowTruncate,
        mem_colTruncate, and_self] using And.intro ⟨hzero,hj⟩ ⟨hzero,hi⟩
    have hpos := Finset.card_pos.mpr ⟨(0,0),hzmem⟩
    have hid := strip_area_identity μ i j
    rw [hcorner, Finset.card_empty, add_zero] at hid
    exact (show μ.card ≤ U+V-1 by omega).trans (le_max_left _ _)

lemma capacity_floor_bound (x f : ℕ) : x ≤ 2*((x-f)/2)+f+1 := by omega

lemma prefix_le_capacity (μ : YoungDiagram) (d q : ℕ) :
    colPrefix μ q ≤ 2*bandCapacity μ d q + q*(d+1) := by
  rw [colPrefix_eq_sum, bandCapacity]
  have h := Finset.sum_le_sum (s := Finset.range q)
    (fun k _ => capacity_floor_bound (μ.colLen k) d)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_add, Nat.mul_one,
    Nat.add_assoc] using h

lemma capacity_large_numeric (M r n : ℕ) (hM : 22 ≤ M) (hr : 2*r ≤ 3*M+4)
    (hn : 2*n = M*(M+1)+4*r) :
    2*(2*r+38) < n ∧ (2*r+38)*(2*r+38) < 64*n := by
  have hM2 := Nat.mul_le_mul_left M hM
  have hr2 := Nat.mul_le_mul hr hr
  constructor <;> nlinarith

theorem capacity_large (μ : YoungDiagram) (M r : ℕ) (hM : 22 ≤ M)
    (hr : 2*r ≤ 3*M+4)
    (hn : μ.card = (staircase M).card + 2*r)
    (hH : 2*M-1 ≤ colPrefix μ 4) (hW : 2*M-1 ≤ rowPrefix μ 4) :
    BandTest M r μ ∨ BandTest M r μ.transpose := by
  classical
  by_contra hh
  push Not at hh
  have ha : (4:ℕ)*8+7+4 ≤ 2*M-1 := by omega
  have hc : bandCapacity μ 4 8 < r := by
    by_contra hc
    exact hh.1 ⟨4, by omega, by omega, 8, by omega, hW, ha, by omega⟩
  have hct : bandCapacity μ.transpose 4 8 < r := by
    by_contra hc
    exact hh.2 ⟨4, by omega, by omega, 8, by omega, hH, ha, by omega⟩
  have h₁ : colPrefix μ 8 ≤ 2*r+38 := by
    have := prefix_le_capacity μ 4 8
    omega
  have h₂ : rowPrefix μ 8 ≤ 2*r+38 := by
    have hp := prefix_le_capacity μ.transpose 4 8
    simp only [colPrefix, YoungDiagram.transpose_transpose] at hp
    omega
  have hb := capacity_rectangle μ (by omega : 0 < 8) (by omega : 0 < 8) h₁ h₂
  have he : 2*μ.card = M*(M+1)+4*r := by
    have hx := staircase_card_double M
    nlinarith
  obtain ⟨hl,hu⟩ := capacity_large_numeric M r μ.card hM hr he
  have hdiv : (2*r+38)*(2*r+38)/(8*8) < μ.card := by
    exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by nlinarith)
  have hmax : max (2*r+38+(2*r+38)-1) ((2*r+38)*(2*r+38)/(8*8)) < μ.card :=
    max_lt (by omega) hdiv
  omega

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceDominance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Dominance. -/

section

noncomputable section

namespace UniversalTensorSquare
open Saxl

lemma rowPrefix_scaled_mono (μ : YoungDiagram) {k l : ℕ} (hkl : k ≤ l) :
    k * rowPrefix μ l ≤ l * rowPrefix μ k := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hl ih =>
    have hlast : k * μ.rowLen l ≤ rowPrefix μ k := by
      have h := Finset.sum_le_sum (s := Finset.range k) (f := fun _ => μ.rowLen l)
        (g := μ.rowLen) (by
          intro i hi
          exact μ.rowLen_anti _ _ (by have := Finset.mem_range.mp hi; omega))
      simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, rowPrefix] using h
    rw [rowPrefix_succ]
    nlinarith

lemma colPrefix_eq_min_sum (μ : YoungDiagram) (k : ℕ) :
    colPrefix μ k = ∑ i ∈ Finset.range (μ.colLen 0), min k (μ.rowLen i) := by
  rw [← colTruncate_card, ← rowPrefix_eq_card _ (colTruncate_height μ k)]
  exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)

lemma scaled_colPrefix_lower (A : YoungDiagram) {k B : ℕ}
    (hB : A.rowLen 0 ≤ B) (hk : k ≤ B) :
    k*A.card ≤ B*colPrefix A k := by
  rw [colPrefix_eq_min_sum, ← rowPrefix_eq_card A le_rfl]
  simp only [rowPrefix, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi : A.rowLen i ≤ B := (A.rowLen_anti _ _ (Nat.zero_le _)).trans hB
  by_cases hh : k ≤ A.rowLen i
  · rw [min_eq_left hh]
    nlinarith
  · rw [min_eq_right (by omega)]
    exact Nat.mul_le_mul_right _ hk

theorem balance_dominance (M : ℕ) (hM : 9 ≤ M) (μ A : YoungDiagram)
    (hc : μ.card = A.card) (hn : (staircase M).card ≤ μ.card)
    (hμ : colPrefix μ 4 ≤ 2*M-2)
    (hparts : 2*M-5 ≤ A.colLen 0) (hmax : A.rowLen 0 ≤ M+1)
    (hfour : 2 ≤ A.rowLen 3) : Dominates μ A := by
  have hdouble := staircase_card_double M
  have hn' : M*(M+1) ≤ 2*μ.card := by omega
  have hlarge : 2*M-2 < μ.card := by
    have hs : M*M ≥ 9*M := Nat.mul_le_mul_right M hM
    have hsub : 2*M-2 ≤ 2*M := Nat.sub_le _ _
    nlinarith
  have hwidth : 4 ≤ μ.rowLen 0 := by
    by_contra hh
    have he : colPrefix μ 4 = μ.card := by
      simpa only [colPrefix, YoungDiagram.colLen_transpose, transpose_card] using
        rowPrefix_eq_card μ.transpose (by simpa using (show μ.rowLen 0 ≤ 4 by omega))
    omega
  have hpos (i : ℕ) (hi : i < 4) : 1 ≤ μ.colLen i := by
    have hh := YoungDiagram.mem_iff_lt_colLen.mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr (show i < μ.rowLen 0 by omega))
    omega
  have hheight : μ.colLen 0 ≤ 2*M-5 := by
    have hp1 := hpos 1 (by decide)
    have hp2 := hpos 2 (by decide)
    have hp3 := hpos 3 (by decide)
    rw [colPrefix_eq_sum] at hμ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hμ
    omega
  have hA1 : 4 ≤ A.colLen 1 := by
    have h := YoungDiagram.mem_iff_lt_colLen.mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr (show 1 < A.rowLen 3 by omega))
    omega
  have hA2 : 2*M-1 ≤ colPrefix A 2 := by
    rw [colPrefix_eq_sum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    omega
  have hdual : Dominates A.transpose μ.transpose := by
    intro k
    change colPrefix μ k ≤ colPrefix A k
    by_cases hk : k < 4
    · interval_cases k
      · simp [colPrefix, rowPrefix]
      · simpa only [colPrefix_eq_sum, Finset.sum_range_one] using hheight.trans hparts
      · exact ((rowPrefix_mono μ.transpose (by omega)).trans hμ).trans (by omega)
      · have hA3 := rowPrefix_mono A.transpose (show 2 ≤ 3 by omega)
        change colPrefix A 2 ≤ colPrefix A 3 at hA3
        exact ((rowPrefix_mono μ.transpose (by omega)).trans hμ).trans (by omega)
    · by_cases hB : A.rowLen 0 ≤ k
      · have he : colPrefix A k = A.card := by
          simpa only [colPrefix, transpose_card] using
            rowPrefix_eq_card A.transpose (by simpa using hB)
        rw [he, ← hc]
        exact (rowPrefix_le_card μ.transpose k).trans_eq (transpose_card _)
      · let B := A.rowLen 0
        have hBp : 0 < B := by dsimp only [B]; omega
        have hupper : 4*colPrefix μ k ≤ k*(2*M-2) :=
          (rowPrefix_scaled_mono μ.transpose (by omega)).trans
            (Nat.mul_le_mul_left k hμ)
        have hlower := scaled_colPrefix_lower A le_rfl (show k ≤ B by dsimp [B]; omega)
        have hratio : B*(2*M-2) ≤ 4*A.card := by
          have hmul := Nat.mul_le_mul_right (2*M-2) hmax
          dsimp only [B]
          have hsub : 2*M-2+2 = 2*M := by omega
          nlinarith
        have hbound : (4*B)*colPrefix μ k ≤ (4*B)*colPrefix A k := calc
          (4*B)*colPrefix μ k = B*(4*colPrefix μ k) := by ring
          _ ≤ B*(k*(2*M-2)) := Nat.mul_le_mul_left B hupper
          _ = k*(B*(2*M-2)) := by ring
          _ ≤ k*(4*A.card) := Nat.mul_le_mul_left k hratio
          _ = 4*(k*A.card) := by ring
          _ ≤ 4*(B*colPrefix A k) := Nat.mul_le_mul_left 4 hlower
          _ = (4*B)*colPrefix A k := by ring
        exact (mul_le_mul_iff_right₀ (show 0 < 4*B by omega)).mp hbound
  simpa only [YoungDiagram.transpose_transpose] using
    dominates_transpose (by simpa only [transpose_card] using hc.symm) hdual

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_CandidateColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Columns. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

lemma oneIf_range {x ε : ℕ} (hε : ε ≤ 1) : oneIf x ε = List.range' x ε := by
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl <;> simp [oneIf,List.range']

lemma balanceColumns_perm {M b δ τ ε m : ℕ}
    (hM : 4 ≤ M) (hτ : τ ≤ 1) (hε : ε ≤ 1) (heq : M = 4+τ+ε+2*m) :
    (balanceColumns M b δ τ ε m).Perm (candidate M b δ).transpose.rowLens := by
  rw [candidate_transpose,candidate_rowLens (by omega)]
  have hrun : oneIf 3 τ ++ oneIf (3+τ) ε ++ List.range' (3+τ+ε) (2*m) =
      List.range' 3 (M-4) := by
    rw [oneIf_range hτ,oneIf_range hε,List.range'_append_1, Nat.add_assoc 3 τ ε,List.range'_append_1]
    congr 1
    omega
  apply List.perm_iff_count.mpr
  intro x
  simp only [balanceColumns,bigColumns,shortColumns,List.count_append,List.count_reverse,
    (pairColumns_perm (3+τ+ε) m).count_eq,show M-1+b+1+δ = M+b+δ by omega]
  have hh := congrArg (List.count x) hrun
  simp only [List.count_append] at hh
  omega

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceFour
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.UniversalTensorSquare.candidateRowShuffle_row _root_.OAI.UniversalTensorSquare.candidateSeparatedRow_row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Four. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns

lemma balanceParts_shape_bounds {M b δ τ ε m : ℕ}
    (hM : 9 ≤ M) (hb : b ≤ M-2) (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1)
    (heq : M = 4+τ+ε+2*m) (hsmall : τ = 0 → 2*(b+1) ≤ M) :
    let θ := (columnShape (balanceParts M b δ τ ε m)).transpose
    2*M-5 ≤ θ.colLen 0 ∧ θ.rowLen 0 ≤ M+1 ∧ 2 ≤ θ.rowLen 3 := by
  let ps := balanceParts M b δ τ ε m
  let θ := (columnShape ps).transpose
  have hp := balanceParts_positive (M := M) (b := b) (δ := δ) (τ := τ) (ε := ε) (m := m) (by omega)
  have hperm := columnShape_rows_permutation ps hp
  have hlen : ps.length = θ.colLen 0 := by
    simpa only [YoungDiagram.length_rowLens] using hperm.length_eq
  have hlower : 2*M-5 ≤ θ.colLen 0 := hlen ▸ balanceParts_length hδ hτ hε heq
  refine ⟨hlower,?_,?_⟩
  · have hzero : 0 < θ.rowLens.length := by rw [YoungDiagram.length_rowLens]; omega
    have hh : θ.rowLen 0 ∈ ps := by
      apply hperm.mem_iff.mpr
      rw [← YoungDiagram.get_rowLens (h := hzero)]
      exact List.getElem_mem hzero
    exact balanceParts_bound (by omega) hb hδ hτ hε heq hsmall hh
  · rw [YoungDiagram.rowLen_transpose]
    change 2 ≤ (columnShape ps).colLen 3
    suffices h : 3 < (columnShape ps).rowLen 1 from
      YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    rw [columnShape_rowLen]
    have hfour : List.countP (fun p => decide (1 < p))
        (balancedParts (2*(M-1+b)+1+3*δ) 4) = 4 := by
      rw [List.countP_eq_length.mpr ?_,balancedParts_length]
      intro p hp
      simp only [decide_eq_true_eq]
      have hh := (balancedParts_part hp).1
      omega
    dsimp only [ps,balanceParts,bigParts]
    simp only [List.countP_append,hfour]
    omega

theorem balance_kronecker_pos {n M b δ : ℕ} (hM : 9 ≤ M)
    (hb : b ≤ M-2) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (μ : YoungDiagram) (s : Tableau n μ)
    (hμ : colPrefix μ 4 ≤ 2*M-2) : 0 < kronecker t t s := by
  let τ := if 2*(b+1) ≤ M then 0 else 1
  let ε := (M-4-τ)%2
  let m := (M-4-τ)/2
  have hτ : τ ≤ 1 := by dsimp [τ]; split_ifs <;> omega
  have hε : ε ≤ 1 := by dsimp [ε]; omega
  have heq : M = 4+τ+ε+2*m := by dsimp [ε,m]; omega
  have hsmall : τ = 0 → 2*(b+1) ≤ M := by
    intro ht
    by_contra h
    have hh : τ = 1 := ite_eq_right h
    omega
  have hshort : τ ≠ 0 → 1 ≤ b := by
    intro ht
    have hn : ¬ 2*(b+1) ≤ M := by
      intro h
      exact ht (ite_eq_left h)
    omega
  have hheight : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ (by omega)]
    simp [candidateLengths]
  have hpack := balancePacking (by omega) hδ hτ hε heq hshort
  rw [← hheight] at hpack
  obtain ⟨A,label,marks,hordered,⟨P⟩⟩ := hpack
  let rs := balanceColumns M b δ τ ε m
  let ps := balanceParts M b δ τ ε m
  have hperm := balanceColumns_perm (b := b) (δ := δ) (by omega) hτ hε heq
  obtain ⟨e,hr,hc⟩ := place_columns (candidate M b δ) hperm
  have hdegree : rs.sum = n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr (((enumerate rs).trans e).trans t.symm)
  subst n
  let a := (enumerate rs).trans e
  have hcand : (candidate M b δ).card = rs.sum := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr a).symm
  have htarget : μ.card = rs.sum := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr s).symm
  have hparts : μ.card = (columnShape ps).transpose.card := by
    rw [htarget,transpose_card,columnShape_card]
    exact P.total.symm
  have hn : (staircase M).card ≤ μ.card := by
    rw [htarget,← hcand,candidate_card _ _ _ (by omega)]
    omega
  obtain ⟨hcount,hmax,hfour⟩ := balanceParts_shape_bounds hM hb hδ hτ hε heq hsmall
  have hdom := balance_dominance M hM μ (columnShape ps).transpose hparts hn hμ hcount hmax hfour
  have hpos := P.kronecker_pos a s (standard_placed_self e hr hc)
    (balanceParts_positive (by omega)) hordered hdom
  unfold kronecker spechtRep Specht at hpos ⊢
  rw [spechtSub_tableau_independent a t] at hpos
  exact hpos

theorem balance_kronecker_pos_or_transpose {n M b δ : ℕ} (hM : 9 ≤ M)
    (hb : b ≤ M-2) (hδ : δ ≤ 1) (hn : (candidate M b δ).card = n)
    (μ : YoungDiagram) (hμ : μ.card = n)
    (hsmall : colPrefix μ 4 ≤ 2*M-2 ∨ colPrefix μ.transpose 4 ≤ 2*M-2) :
    0 < kronecker (canonicalTableau (candidate M b δ) hn)
      (canonicalTableau (candidate M b δ) hn) (canonicalTableau μ hμ) := by
  rcases hsmall with h | h
  · exact balance_kronecker_pos hM hb hδ _ μ _ h
  · have hpos := balance_kronecker_pos hM hb hδ (canonicalTableau (candidate M b δ) hn)
      μ.transpose (canonicalTableau μ.transpose ((transpose_card μ).trans hμ)) h
    exact (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr hpos

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Criterion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

theorem fixedCandidate_band_pos (n : ℕ) (hM : 4 ≤ staircaseIndex n)
    (μ : YoungDiagram) (hμ : μ.card = n)
    (hband : BandTest (staircaseIndex n) (remainderPairs n) μ) :
    0 < kronecker (canonicalTableau (fixedCandidate n) (fixedCandidate_card n (by omega)))
      (canonicalTableau (fixedCandidate n) (fixedCandidate_card n (by omega)))
      (canonicalTableau μ hμ) := by
  have hδ : remainderPairs n % 2 ≤ 1 := by omega
  have hr : remainderPairs n = 2 * (remainderPairs n / 2) + remainderPairs n % 2 := by omega
  exact band_kronecker_pos (M := staircaseIndex n) (b := remainderPairs n / 2)
    (δ := remainderPairs n % 2) (r := remainderPairs n) hM hδ hr
    (canonicalTableau (fixedCandidate n) (fixedCandidate_card n (by omega)))
    μ (canonicalTableau μ hμ) hband

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Intermediate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intermediate. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma testWidth_valid {M f : ℕ} (hM : 9 ≤ M) (hf : 1 ≤ f) (hf' : f ≤ 4) :
    testWidth M f ≤ 8 ∧ f * testWidth M f + 7 + f ≤ 2*M-1 := by
  refine ⟨min_le_left _ _, ?_⟩
  have h := Nat.mul_le_mul_left f (min_le_right 8 ((2*M-8-f)/f))
  have h' := Nat.div_mul_le_self (2*M-8-f) f
  unfold testWidth
  nlinarith [Nat.sub_add_cancel (show f ≤ 2*M-8 by omega),
    Nat.sub_add_cancel (show 8 ≤ 2*M by omega),
    Nat.sub_add_cancel (show 1 ≤ 2*M by omega)]

lemma prefixBounds_sound (μ : YoungDiagram) {M r d e : ℕ}
    (hM : 9 ≤ M) (hr : 0 < r)
    (hd : 1 < d → colPrefix μ (d-1) < 2*M-1)
    (he : 2*M-1 ≤ rowPrefix μ e) (hfail : ¬BandTest M r μ) :
    ∀ p ∈ prefixBounds M r d e, 0 < p.1 ∧ colPrefix μ p.1 ≤ p.2 := by
  intro p hp
  simp only [prefixBounds, List.mem_append] at hp
  rcases hp with hp | hp
  · split_ifs at hp with hd'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst p
      exact ⟨by omega, by have := hd hd'; dsimp; omega⟩
    · simp at hp
  · obtain ⟨k,hk,hkp⟩ := List.mem_filterMap.mp hp
    simp only [List.mem_range] at hk
    split_ifs at hkp with hke
    · have hp' := Option.some.inj hkp
      subst p
      have hw := testWidth_valid hM (by omega : 1 ≤ k+1) (by omega : k+1 ≤ 4)
      have hc : bandCapacity μ (k+1) (testWidth M (k+1)) < r := by
        by_contra hh
        apply hfail
        exact ⟨k+1, by omega, by omega, testWidth M (k+1), hw.1,
          he.trans (rowPrefix_mono μ hke.1), hw.2, by omega⟩
      have hb := prefix_le_capacity μ (k+1) (testWidth M (k+1))
      exact ⟨hke.2, by dsimp; omega⟩

lemma intermediate9 : ∀ r ∈ List.range 34, admissibleR 9 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 9 r (d+1) (e+1) := by decide

lemma intermediate10 : ∀ r ∈ List.range 34, admissibleR 10 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 10 r (d+1) (e+1) := by decide

lemma intermediate11 : ∀ r ∈ List.range 34, admissibleR 11 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 11 r (d+1) (e+1) := by decide

lemma intermediate12 : ∀ r ∈ List.range 34, admissibleR 12 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 12 r (d+1) (e+1) := by decide

lemma intermediate13 : ∀ r ∈ List.range 34, admissibleR 13 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 13 r (d+1) (e+1) := by decide

lemma intermediate14 : ∀ r ∈ List.range 34, admissibleR 14 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 14 r (d+1) (e+1) := by decide

lemma intermediate15 : ∀ r ∈ List.range 34, admissibleR 15 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 15 r (d+1) (e+1) := by decide

lemma intermediate16 : ∀ r ∈ List.range 34, admissibleR 16 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 16 r (d+1) (e+1) := by decide

lemma intermediate17 : ∀ r ∈ List.range 34, admissibleR 17 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 17 r (d+1) (e+1) := by decide

lemma intermediate18 : ∀ r ∈ List.range 34, admissibleR 18 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 18 r (d+1) (e+1) := by decide

lemma intermediate19 : ∀ r ∈ List.range 34, admissibleR 19 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 19 r (d+1) (e+1) := by decide

lemma intermediate20 : ∀ r ∈ List.range 34, admissibleR 20 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 20 r (d+1) (e+1) := by decide

lemma intermediate21 : ∀ r ∈ List.range 34, admissibleR 21 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 21 r (d+1) (e+1) := by decide

lemma capacity_intermediate_numeric {M r d e : ℕ}
    (hM : 9 ≤ M) (hM' : M ≤ 21) (hr : admissibleR M r)
    (hd : 1 ≤ d) (hd' : d ≤ 4) (he : 1 ≤ e) (he' : e ≤ 4) :
    intermediateCheck M r d e := by
  have hr' : r ∈ List.range 34 := by
    have hb := hr.2.1
    split_ifs at hb <;> simp only [List.mem_range] <;> omega
  have hdd : d-1 ∈ List.range 4 := by simp only [List.mem_range]; omega
  have hee : e-1 ∈ List.range 4 := by simp only [List.mem_range]; omega
  have hde : d = (d-1)+1 := by omega
  have hee' : e = (e-1)+1 := by omega
  rw [hde, hee']
  interval_cases M
  · exact intermediate9 r hr' hr _ hdd _ hee
  · exact intermediate10 r hr' hr _ hdd _ hee
  · exact intermediate11 r hr' hr _ hdd _ hee
  · exact intermediate12 r hr' hr _ hdd _ hee
  · exact intermediate13 r hr' hr _ hdd _ hee
  · exact intermediate14 r hr' hr _ hdd _ hee
  · exact intermediate15 r hr' hr _ hdd _ hee
  · exact intermediate16 r hr' hr _ hdd _ hee
  · exact intermediate17 r hr' hr _ hdd _ hee
  · exact intermediate18 r hr' hr _ hdd _ hee
  · exact intermediate19 r hr' hr _ hdd _ hee
  · exact intermediate20 r hr' hr _ hdd _ hee
  · exact intermediate21 r hr' hr _ hdd _ hee

lemma first_prefix_height (μ : YoungDiagram) {K : ℕ} (hK : 0 < K)
    (h : K ≤ rowPrefix μ 4) :
    ∃ d, 1 ≤ d ∧ d ≤ 4 ∧ K ≤ rowPrefix μ d ∧
      (1 < d → rowPrefix μ (d-1) < K) := by
  let h' : ∃ d, K ≤ rowPrefix μ d := ⟨4,h⟩
  refine ⟨Nat.find h', ?_, Nat.find_min' h' h, Nat.find_spec h', ?_⟩
  · have hx := Nat.find_spec h'
    by_contra hh
    have hd : Nat.find h' = 0 := by omega
    change K ≤ rowPrefix μ (Nat.find h') at hx
    rw [hd] at hx
    simp only [rowPrefix, Finset.range_zero, Finset.sum_empty] at hx
    omega
  · intro hd
    exact Nat.lt_of_not_ge (Nat.find_min h' (by omega))

theorem capacity_intermediate (μ : YoungDiagram) {M r : ℕ}
    (hM : 9 ≤ M) (hM' : M ≤ 21) (hr : admissibleR M r)
    (hn : μ.card = (staircase M).card + 2*r)
    (hH : 2*M-1 ≤ colPrefix μ 4) (hW : 2*M-1 ≤ rowPrefix μ 4) :
    BandTest M r μ ∨ BandTest M r μ.transpose := by
  classical
  by_contra hh
  push Not at hh
  obtain ⟨d,hd,hd',hHd,hHd'⟩ := first_prefix_height μ.transpose (by omega) hH
  obtain ⟨e,he,he',hWe,hWe'⟩ := first_prefix_height μ (by omega) hW
  obtain ⟨p,hp,q,hq,hpq⟩ := capacity_intermediate_numeric hM hM' hr hd hd' he he'
  have hp' := prefixBounds_sound μ hM hr.1 hHd' hWe hh.1 p hp
  have hq' := prefixBounds_sound μ.transpose hM hr.1
    (by simpa only [colPrefix, YoungDiagram.transpose_transpose] using hWe')
    hHd hh.2 q hq
  have hb := capacity_rectangle μ hp'.1 hq'.1 hp'.2
    (by simpa only [colPrefix, YoungDiagram.transpose_transpose] using hq'.2)
  have hn' : μ.card = M*(M+1)/2+2*r := by rw [hn, staircase_card]
  omega

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_CapacityDichotomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capacity Dichotomy. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

theorem capacity_dichotomy (μ : YoungDiagram) {M r : ℕ}
    (hM : 9 ≤ M) (hr : 0 < r)
    (hbound : if M % 2 = 1 then 2*r ≤ M-1 else 2*r ≤ 3*M+4)
    (hexc : ¬exceptionalPair M r)
    (hn : μ.card = (staircase M).card + 2*r) :
    colPrefix μ 4 ≤ 2*M-2 ∨ colPrefix μ.transpose 4 ≤ 2*M-2 ∨
      BandTest M r μ ∨ BandTest M r μ.transpose := by
  by_cases hs : colPrefix μ 4 ≤ 2*M-2
  · exact Or.inl hs
  apply Or.inr
  by_cases ht : colPrefix μ.transpose 4 ≤ 2*M-2
  · exact Or.inl ht
  apply Or.inr
  have hH : 2*M-1 ≤ colPrefix μ 4 := by omega
  have hW : 2*M-1 ≤ rowPrefix μ 4 := by
    simp only [colPrefix, YoungDiagram.transpose_transpose] at ht
    omega
  by_cases hlarge : 22 ≤ M
  · apply capacity_large μ M r hlarge _ hn hH hW
    split_ifs at hbound <;> omega
  · exact capacity_intermediate μ hM (by omega) ⟨hr,hbound,hexc⟩ hn hH hW

theorem fixed_degree_capacity_dichotomy (n : ℕ) (hn : 64 < n)
    (hr : 0 < remainderPairs n)
    (hexc : ¬exceptionalPair (staircaseIndex n) (remainderPairs n))
    (μ : YoungDiagram) (hμ : μ.card = n) :
    colPrefix μ 4 ≤ 2*staircaseIndex n-2 ∨
      colPrefix μ.transpose 4 ≤ 2*staircaseIndex n-2 ∨
      BandTest (staircaseIndex n) (remainderPairs n) μ ∨
      BandTest (staircaseIndex n) (remainderPairs n) μ.transpose := by
  have hM : 9 ≤ staircaseIndex n := by
    by_contra h
    have := degree_le_64_of_small_index n (by omega)
    omega
  apply capacity_dichotomy μ hM hr _ hexc
    (hμ.trans (degree_eq n).symm)
  split_ifs with ho
  · exact remainderPairs_bound_odd n ho
  · exact remainderPairs_bound_even n (by omega)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_Asymptotic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Asymptotic. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma remainderPairs_bound (n : ℕ) : 2*remainderPairs n ≤ 3*staircaseIndex n+4 := by
  rcases Nat.mod_two_eq_zero_or_one (staircaseIndex n) with he | ho
  · exact remainderPairs_bound_even n he
  · have h := remainderPairs_bound_odd n ho
    omega

lemma fixedCandidate_half_bound (n : ℕ) (hM : 9 ≤ staircaseIndex n) :
    remainderPairs n / 2 ≤ staircaseIndex n-2 := by
  have h := remainderPairs_bound n
  omega

lemma canonical_square_pos_congr {n N : ℕ} {lam Lam μ : YoungDiagram}
    (he : n = N) (hlam : lam = Lam) (hc : lam.card = n) (hC : Lam.card = N)
    (hμ : μ.card = n) (hμ' : μ.card = N) :
    (0 < kronecker (canonicalTableau lam hc) (canonicalTableau lam hc) (canonicalTableau μ hμ)) ↔
      (0 < kronecker (canonicalTableau Lam hC) (canonicalTableau Lam hC) (canonicalTableau μ hμ')) := by
  subst N
  subst Lam
  rfl

theorem fixedCandidate_nonexceptional_pos (n : ℕ) (hn : 64 < n)
    (hexc : ¬ exceptionalPair (staircaseIndex n) (remainderPairs n))
    (μ : YoungDiagram) (hμ : μ.card = n) :
    0 < kronecker (canonicalTableau (fixedCandidate n)
      (fixedCandidate_card n (by have := (fixedCandidate_large_degree n hn).1; omega)))
      (canonicalTableau (fixedCandidate n)
        (fixedCandidate_card n (by have := (fixedCandidate_large_degree n hn).1; omega)))
      (canonicalTableau μ hμ) := by
  have hM := (fixedCandidate_large_degree n hn).1
  by_cases hr : remainderPairs n = 0
  · have he : n = staircaseIndex n * (staircaseIndex n+1)/2 := by
      have h := degree_eq n
      rw [hr,staircase_card] at h
      omega
    apply (canonical_square_pos_congr he
      (fixedCandidate_eq_staircase_of_remainder_zero n hr) _
      (staircase_card (staircaseIndex n)) hμ (hμ.trans he)).mpr
    exact saxl_kronecker_pos (staircaseIndex n) (by omega) μ (hμ.trans he)
  · rcases fixed_degree_capacity_dichotomy n hn (by omega) hexc μ hμ with
      h | h | h | h
    · exact balance_kronecker_pos hM (fixedCandidate_half_bound n hM) (by omega)
        _ μ _ h
    · exact balance_kronecker_pos_or_transpose hM (fixedCandidate_half_bound n hM)
        (by omega) _ μ hμ (Or.inr h)
    · exact fixedCandidate_band_pos n (by omega) μ hμ h
    · apply (fixedCandidate_support_transpose n (by omega) μ hμ).mpr
      exact fixedCandidate_band_pos n (by omega) μ.transpose ((transpose_card μ).trans hμ) h

universe u

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Universal tensor squares. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

universe u

theorem universal_tensor_square
    (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = n),
      (∀ (ν : YoungDiagram) (hν : ν.card = n),
        0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
          (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
            (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
          Function.Injective F := by
  have hex : ∃ (lam : YoungDiagram) (hc : lam.card = n),
      ∀ (μ : YoungDiagram) (hμ : μ.card = n),
        0 < kronecker (canonicalTableau lam hc) (canonicalTableau lam hc)
          (canonicalTableau μ hμ) := by
    by_cases hsmall : n ≤ 64
    · exact universal_partition_le64 n hn h2 h4 h9 hsmall
    · have hlarge : 64 < n := by omega
      by_cases hexc : exceptionalPair (staircaseIndex n) (remainderPairs n)
      · exact universal_partition_exceptional n hexc
      · have hM := (fixedCandidate_large_degree n hlarge).1
        exact ⟨fixedCandidate n,fixedCandidate_card n (by omega),
          fixedCandidate_nonexceptional_pos n hlarge hexc⟩
  obtain ⟨lam,hc,hpos⟩ := hex
  exact ⟨lam,hc,hpos,irreducibles_of_kronecker_pos lam hc hpos⟩

end UniversalTensorSquare
end
end

namespace UniversalTensorSquares
universe u
theorem universal_tensor_square_oai
    (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = n),
      (∀ (ν : YoungDiagram) (hν : ν.card = n),
        0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
          (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
            (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
          Function.Injective F := by
  exact UniversalTensorSquare.universal_tensor_square n hn h2 h4 h9
end UniversalTensorSquares

end OAI
end

theorem solution.{u} : type_of% @OAI.UniversalTensorSquares.universal_tensor_square_oai.{u} := @OAI.UniversalTensorSquares.universal_tensor_square_oai.{u}
