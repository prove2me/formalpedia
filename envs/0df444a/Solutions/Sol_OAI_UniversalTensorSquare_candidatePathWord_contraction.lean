-- Prove2me | solution 1 for OAI.UniversalTensorSquare.candidatePathWord_contraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:36:57.061557+00:00
-- url     : https://prove2.me/submissions/d44f785b-f0b0-47c0-bc9d-9539f595deeb

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_Band_blocks_scaled

section
-- module Solutions.OAIQ259_US.Saxl_PositionSplit
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.joinPositions_parts _root_.OAI.Saxl.leftWord_join _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.rightWord_join _root_.OAI.Saxl.sumPerm_mul _root_.OAI.Saxl.sumPerm_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/

lemma altWord_split_term {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w v : Fin n → Fin d) (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    (signC (sumPerm e g h) • wordRep n d (sumPerm e g h) (Pi.single w 1)) v =
    (signC g • wordRep a d g (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC h • wordRep b d h (Pi.single (rightWord e w) 1)) (rightWord e v) := by
  rw [single_positionProduct e w]
  change signC (sumPerm e g h) *
    ((Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e (v ∘ sumPerm e g h)) *
      (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e (v ∘ sumPerm e g h))) = _
  have h₁ : leftWord e (v ∘ sumPerm e g h) = leftWord e v ∘ g := by
    ext i; simp [leftWord]
  have h₂ : rightWord e (v ∘ sumPerm e g h) = rightWord e v ∘ h := by
    ext i; simp [rightWord]
  rw [h₁,h₂,signC_sumPerm]
  change _ = (signC g * (Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e v ∘ g)) *
    (signC h * (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e v ∘ h))
  ring

/- Independent block permutations factor with exactly the product sign. -/
theorem altWord_split {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (G : Subgroup (Equiv.Perm (Fin n))) (G₁ : Subgroup (Equiv.Perm (Fin a)))
    (G₂ : Subgroup (Equiv.Perm (Fin b))) (E : G ≃ G₁ × G₂)
    (hE : ∀ g : G, (g : Equiv.Perm (Fin n)) =
      sumPerm e ((E g).1 : Equiv.Perm (Fin a)) ((E g).2 : Equiv.Perm (Fin b)))
    (w : Fin n → Fin d) :
    altWord G w = positionProduct e (altWord G₁ (leftWord e w)) (altWord G₂ (rightWord e w)) := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite G₁
  let := Fintype.ofFinite G₂
  ext v
  unfold altWord
  simp only [Finset.sum_apply, positionProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : G₁ × G₂,
      (signC (p.1 : Equiv.Perm (Fin a)) • wordRep a d p.1 (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC (p.2 : Equiv.Perm (Fin b)) • wordRep b d p.2 (Pi.single (rightWord e w) 1)) (rightWord e v) := by
        apply Fintype.sum_equiv E
        intro g
        rw [hE g]
        exact altWord_split_term e w v _ _
    _ = _ := Fintype.sum_prod_type _



theorem altWord_fiber_split {n a b d : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin a ⊕ Fin b)
    (f : Fin n → α) (w : Fin n → Fin d) :
    altWord (fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) w =
      positionProduct e
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inl i)))) (leftWord e w))
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inr i)))) (rightWord e w)) := by
  apply altWord_split e _ _ _ (fiberSplit e f).symm
  intro g
  exact (congrArg Subtype.val ((fiberSplit e f).apply_symm_apply g)).symm


end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PathAlternation
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.joinPositions_parts _root_.OAI.Saxl.leftWord_join _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.rightWord_join
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl.PathLayer

lemma tag_left (r : ℕ) (i : Fin (2*r+1)) :
    tag ((appendPair r).symm (Sum.inl i)) = tag i := rfl
lemma tag_right (r : ℕ) (i : Fin 2) :
    tag ((appendPair r).symm (Sum.inr i)) = r+1 := by
  unfold tag
  rw [appendPair_right]
  omega

lemma tag_side (r : ℕ) (i : Fin (2*(r+1)+1)) :
    (appendPair r i).isLeft = true ↔ tag i < r+1 := by
  obtain ⟨j,rfl⟩ := (appendPair r).symm.surjective i
  cases j with
  | inl j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, true_iff, tag_left]; unfold tag; omega
  | inr j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, tag_right, lt_self_iff_false]

lemma rowGroup_sector (r : ℕ) :
    Saxl.fiberGroup (@tag (r+1)) = Saxl.fiberGroup (@tag (r+1)) ⊓
      Saxl.sectorGroup (fun i => (appendPair r i).isLeft = true) := by
  apply le_antisymm
  · intro g hg
    refine ⟨hg, ?_⟩
    intro i
    change (appendPair r (g i)).isLeft = true ↔ (appendPair r i).isLeft = true
    rw [tag_side,tag_side]
    change ∀ i, tag (g i) = tag i at hg
    rw [hg]
  · exact inf_le_left

lemma rowAlt_step (r : ℕ) :
    rowAlt (r+1) = Saxl.positionProduct (appendPair r) (rowAlt r)
      (Saxl.altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i)) := by
  unfold rowAlt
  rw [rowGroup_sector, Saxl.altWord_fiber_split]
  have hl : Saxl.fiberGroup (fun i => tag ((appendPair r).symm (Sum.inl i))) =
      Saxl.fiberGroup (@tag r) := rfl
  have hr : Saxl.fiberGroup (fun i => tag ((appendPair r).symm (Sum.inr i))) = ⊤ := by
    apply Subgroup.ext
    intro g
    change (∀ i, tag ((appendPair r).symm (Sum.inr (g i))) = tag ((appendPair r).symm (Sum.inr i))) ↔ True
    simp only [tag_right, implies_true]
  rw [hl,hr]
  congr 2
  funext i
  apply Fin.ext
  change (base ((appendPair r).symm (Sum.inr i))).val = i.val
  have hn : ((appendPair r).symm (Sum.inr i)).val ≠ 0 := by rw [appendPair_right]; omega
  unfold base
  rw [ite_eq_right hn]
  change (2*r+1+i.val+1)%2 = i.val
  omega

lemma pair_alt (w : Fin 2 → Fin 2) :
    Saxl.altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i) w = J (w 0) (w 1) := by
  classical
  let := Fintype.ofFinite (⊤ : Subgroup (Equiv.Perm (Fin 2)))
  unfold Saxl.altWord
  rw [Finset.sum_apply]
  change (∑ g : (⊤ : Subgroup (Equiv.Perm (Fin 2))), Saxl.signC (g : Equiv.Perm (Fin 2)) *
    ((Pi.single (fun i : Fin 2 => i) (1:ℂ) : Saxl.WordSpace 2 2) (w ∘ (g : Equiv.Perm (Fin 2))))) = _
  calc
    _ = ∑ g : Equiv.Perm (Fin 2), Saxl.signC g *
        ((Pi.single (fun i : Fin 2 => i) (1:ℂ) : Saxl.WordSpace 2 2) (w ∘ g)) :=
      Fintype.sum_equiv (Subgroup.topEquiv (G := Equiv.Perm (Fin 2))).toEquiv _ _ (by intro g; rfl)
    _ = _ := by
      have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1,Equiv.swap 0 1} := by decide
      rw [hu]
      have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
      simp only [Finset.sum_insert (Finset.notMem_singleton.mpr hne), Finset.sum_singleton]
      have hw : w = ![w 0,w 1] := by ext i; fin_cases i <;> rfl
      rw [hw]
      generalize h0 : w 0 = a
      generalize h1 : w 1 = b
      fin_cases a <;> fin_cases b <;>
        (first | (simp [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]; all_goals first | (norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]; done) | rfl | decide) | (norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]; done) | norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J])

lemma rowAlt_zero (w : Fin 1 → Fin 2) :
    rowAlt 0 w = if w 0 = 0 then 1 else 0 := by
  classical
  change Saxl.altWord (Saxl.fiberGroup (@tag 0)) (@base 0) w = _
  let := Fintype.ofFinite (Saxl.fiberGroup (@tag 0))
  unfold Saxl.altWord
  have hu : (Finset.univ : Finset (Saxl.fiberGroup (@tag 0))) = {1} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Fin.ext
    have := ((g : Equiv.Perm (Fin (2*0+1))) i).isLt
    have := i.isLt
    omega
  rw [hu,Finset.sum_singleton]
  simp only [OneMemClass.coe_one, map_one, one_smul]
  change (Pi.single (@base 0) (1:ℂ) : Saxl.WordSpace 1 2) w = _
  rw [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; have := congrFun h 0; simpa [base] using this
  · intro h; funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; simpa [base] using h

lemma rowAlt_formula (r : ℕ) (w : Fin (2*r+1) → Fin 2) :
    rowAlt r w = (if w 0 = 0 then 1 else 0) *
      ∏ i : Fin r, J (w ⟨2*i.val+1,by omega⟩) (w ⟨2*i.val+2,by omega⟩) := by
  induction r with
  | zero => simpa using rowAlt_zero w
  | succ r ih =>
    rw [rowAlt_step]
    change rowAlt r (Saxl.leftWord (appendPair r) w) *
      Saxl.altWord ⊤ (fun i : Fin 2 => i) (Saxl.rightWord (appendPair r) w) = _
    rw [ih, pair_alt, Fin.prod_univ_castSucc]
    exact mul_assoc _ _ _

end Saxl.PathLayer

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
-- module Solutions.OAIQ259_US.Saxl_BandMatrices
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uA

namespace Saxl.Band

lemma Q_inverse : Q⁻¹ = Qinv := by
  exact Matrix.inv_eq_left_inv Qinv_mul_Q

lemma Q_basis_ne_zero (i : Fin 4) : (Q * basis i.val * Q⁻¹) 0 0 ≠ 0 := by
  rw [Q_inverse]
  fin_cases i <;> (first | (simp [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two])

/- Endpoint noncancellation for arbitrary consecutive columns of lengths at most four. -/

end Saxl.Band

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PathContraction
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Path

lemma chainML_apply (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = (List.ofFn fun i => Band.D (p + i.val) (X i)).prod := rfl

lemma entry_sum (X : Mat) :
    (∑ a : Letter, X (parts a).1 (parts a).2 • entry a) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; all_goals first | (norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | rfl | decide) | (norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff])

lemma chain_expand (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = ∑ w : Fin n → Letter, pureWord X w •
      chainML n p (fun i => entry (w i)) := by
  calc
    chainML n p X = chainML n p (fun i => ∑ a : Letter,
      X i (parts a).1 (parts a).2 • entry a) := by
        congr 1; funext i; exact (entry_sum (X i)).symm
    _ = _ := ?_
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [MultilinearMap.map_smul_univ]
  rfl

lemma adj_entry (a : Letter) (i j : Fin 2) :
    (entry a).adjugate i j = -(J i (parts a).2 * J (parts a).1 j) := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    (first | (simp [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; all_goals first | (norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | rfl | decide) | (norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff])

lemma D_shift (q : ℕ) (X : Mat) : Band.D (q + 2) X = Band.D q X := by
  simp [Band.D]

lemma chain_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    chainML (2 * (r+1) + 1) 1 (fun i => entry (w i)) =
      entry (w 0) * (entry (w 1)).adjugate *
      chainML (2 * r + 1) 1 (fun i => entry (w i.succ.succ)) := by
  rw [chainML_apply, List.ofFn_succ, List.prod_cons, List.ofFn_succ,
    List.prod_cons, chainML_apply]
  simp only [Fin.val_zero, Fin.val_succ, add_zero]
  rw [show Band.D 1 = id from by funext X; simp [Band.D],
    show Band.D 2 = Matrix.adjugate from by funext X; simp [Band.D]]
  simp only [id_eq]
  rw [mul_assoc]
  apply congrArg (fun A : Mat => entry (w 0) * ((entry (w 1)).adjugate * A))
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  rw [show 1 + (i.val + 1 + 1) = (1 + i.val) + 2 by omega, D_shift]

lemma pair_product_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    (∏ i : Fin (r+1), J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) =
    (J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1) *
    ∏ i : Fin r, J (parts (w (leftPos i).succ.succ)).2
      (parts (w (midPos i).succ.succ)).2 *
      J (parts (w (midPos i).succ.succ)).1 (parts (w (rightPos i).succ.succ)).1 := by
  rw [Fin.prod_univ_succ]
  rfl

lemma chain_entries (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) =
    ((-1 : ℂ)^r * ∏ i : Fin r,
      J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) •
    Matrix.single (parts (w 0)).1 (parts (w (Fin.last (2*r)))).2 1 := by
  induction r with
  | zero => simp [chainML_apply, List.ofFn_succ, Band.D, entry]
  | succ r ih =>
    rw [chain_step, ih, Matrix.mul_smul, pair_product_step]
    rw [show (0 : Fin (2*r+1)).succ.succ = 2 from Fin.ext rfl]
    change _ = _ • Matrix.single _ (parts (w (Fin.last (2*r)).succ.succ)).2 1
    unfold entry at *
    rw [Matrix.single_mul_mul_single, one_mul, mul_one]
    rw [show (Matrix.single (parts (w 1)).1 (parts (w 1)).2 (1 : ℂ)).adjugate
      (parts (w 0)).2 (parts (w 2)).1 =
      -(J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1)
      from adj_entry (w 1) _ _]
    rw [show ∀ (c : ℂ) (i j : Fin 2), Matrix.single i j c = c • Matrix.single i j 1
      from fun c i j => by ext a b; simp [Matrix.single, smul_eq_mul]]
    rw [smul_smul]
    congr 1
    rw [pow_succ]
    ring

lemma chain_entries_endpoint (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) 0 0 =
      (-1 : ℂ)^r * bandWord r w := by
  rw [chain_entries]
  by_cases h₁ : (parts (w 0)).1 = 0 <;>
    by_cases h₂ : (parts (w (Fin.last (2*r)))).2 = 0 <;>
    simp [bandWord, Matrix.single, h₁, h₂]

end Saxl.Path

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

lemma chain_cons (r : ℕ) (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat)
    (π : Equiv.Perm (Fin r)) (σ : Perms rs) :
    chain (r :: rs) p N (π, σ) =
      (List.ofFn fun j : Fin r => Band.D (p + j.val) (N (π j).val)).prod *
      chain rs (p + r) N σ := by
  unfold chain
  erw [List.ofFn_add, List.prod_append]
  congr 2
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + j.val) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.castAdd rs.sum j))))) = _
    rw [enumerate_left]
    rfl
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + (r + j.val)) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.natAdd r j))))) = _
    erw [enumerate_right r rs (show Fin rs.sum from j)]
    simp only [perm, Equiv.sumCongr_apply, Sum.map_inr, row, Nat.add_assoc]

/- Ordered product of independent alternating column segments. -/
lemma sum_chain (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat) :
    (∑ π : Perms rs, sg π • chain rs p N π) = segments p rs N := by
  induction rs generalizing p with
  | nil => simp [Perms, chain, sg, segments]
  | cons r rs ih =>
    simp only [Perms, Fintype.sum_prod_type, sg, chain_cons, segments]
    simp_rw [← smul_mul_smul_comm, ← Finset.mul_sum, ← Finset.sum_mul, ih]

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandPairing
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Band

lemma conjugation_one : conjugation 1 = 1 := by
  change Q * 1 * Qinv = 1
  rw [mul_one, Q_mul_Qinv]

lemma conjugation_mul (X Y : Mat) : conjugation (X * Y) = conjugation X * conjugation Y := by
  change Q * (X * Y) * Qinv = (Q * X * Qinv) * (Q * Y * Qinv)
  simp only [mul_assoc, ← mul_assoc Qinv Q, Qinv_mul_Q, one_mul]

lemma conjugation_D (q : ℕ) (X : Mat) : D q (conjugation X) = conjugation (D q X) := by
  by_cases h : q % 2 = 0
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, h, conjugation, Q, Qinv, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
  · simp [D, h]

lemma conjugation_prod (l : List Mat) : (l.map conjugation).prod = conjugation l.prod := by
  induction l with
  | nil => simp [conjugation_one]
  | cons a l ih => simp [ih, conjugation_mul]

lemma segments_conjugation (rs : List ℕ) (p : ℕ) :
    Columns.segments p rs (fun i => conjugation (basis i)) = conjugation (blocks p rs) := by
  induction rs generalizing p with
  | nil => exact conjugation_one.symm
  | cons r rs ih =>
    simp only [Columns.segments, blocks, ih, conjugation_mul]
    congr 1
    unfold segment
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro π hπ
    rw [map_smul]
    congr 1
    simp_rw [conjugation_D]
    have he := conjugation_prod (List.ofFn fun j : Fin r => D (p + j.val) (basis (π j).val))
    rw [List.map_ofFn] at he
    exact he

lemma conjugation_blocks_ne_zero (rs : List ℕ)
    (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) : conjugation (blocks 1 rs) 0 0 ≠ 0 := by
  obtain ⟨c, hc, i, hi⟩ := blocks_scaled rs hrs 1
  rw [hi, map_smul]
  apply mul_ne_zero hc
  simpa only [conjugation, LinearMap.coe_mk, AddHom.coe_mk, Q_inverse] using Q_basis_ne_zero i

end Saxl.Band
namespace Saxl.Path

lemma chainFunctional_pure (n p : ℕ) (X : Fin n → Mat) :
    chainFunctional n p (pureWord X) = chainML n p X := (chain_expand n p X).symm

lemma chainFunctional_endpoint (r : ℕ) (x : WordSpace (2*r+1) 4) :
    chainFunctional (2*r+1) 1 x 0 0 = (-1 : ℂ)^r * dotProduct x (bandWord r) := by
  change (∑ w : Fin (2*r+1) → Fin 4,
    x w • chainML (2*r+1) 1 (fun i => entry (w i))) 0 0 = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, chain_entries_endpoint]
  simp [dotProduct, Finset.mul_sum, mul_left_comm]


end Saxl.Path

namespace Saxl.PathLayer

lemma J_flip (a b : Fin 2) : J a b = - J b a := by
  fin_cases a <;> fin_cases b <;> (first | (simp [J]; all_goals first | (norm_num [J]; done) | rfl | decide) | (norm_num [J]; done) | norm_num [J])

lemma rowAlt_rev_formula (r : ℕ) (w : Fin (2*r+1) → Fin 2) :
    rowAlt r (w ∘ Fin.rev) = (if w (Fin.last (2*r)) = 0 then 1 else 0) *
      ((-1 : ℂ)^r * ∏ i : Fin r, J (w ⟨2*i.val,by omega⟩) (w ⟨2*i.val+1,by omega⟩)) := by
  rw [rowAlt_formula]
  have hzero : (0 : Fin (2*r+1)).rev = Fin.last (2*r) := by apply Fin.ext; simp
  simp only [Function.comp_apply, hzero]
  congr 1
  calc
    (∏ i : Fin r, J (w (⟨2*i.val+1,by omega⟩ : Fin (2*r+1)).rev)
      (w (⟨2*i.val+2,by omega⟩ : Fin (2*r+1)).rev)) =
      ∏ i : Fin r, (-1 : ℂ) * J (w ⟨2*i.val,by omega⟩) (w ⟨2*i.val+1,by omega⟩) := by
        apply Fintype.prod_equiv Fin.revPerm
        intro i
        have h₁ : (⟨2*i.val+1,by omega⟩ : Fin (2*r+1)).rev = ⟨2*i.rev.val+1,by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_rev]; have := i.isLt; omega
        have h₂ : (⟨2*i.val+2,by omega⟩ : Fin (2*r+1)).rev = ⟨2*i.rev.val,by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_rev]; have := i.isLt; omega
        rw [h₁,h₂,J_flip]
        simp
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

theorem paired_rowAlt (r : ℕ) (w : Fin (2*r+1) → Saxl.Path.Letter) :
    rowAlt r (fun i => (Saxl.Path.parts (w i)).1) *
      rowAlt r ((fun i => (Saxl.Path.parts (w i)).2) ∘ Fin.rev) =
      (-1 : ℂ)^r * Saxl.Path.bandWord r w := by
  rw [rowAlt_formula,rowAlt_rev_formula]
  unfold Saxl.Path.bandWord
  rw [Finset.prod_mul_distrib]
  change _ = (-1:ℂ)^r * (_ * _ *
    ((∏ i : Fin r, J (Saxl.Path.parts (w ⟨2*i.val,by omega⟩)).2 (Saxl.Path.parts (w ⟨2*i.val+1,by omega⟩)).2) *
     (∏ i : Fin r, J (Saxl.Path.parts (w ⟨2*i.val+1,by omega⟩)).1 (Saxl.Path.parts (w ⟨2*i.val+2,by omega⟩)).1)))
  ring

end Saxl.PathLayer

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SymmetricPairs
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma letterLift_pair {n a b : ℕ} (φ : Fin a → Fin b)
    (x : WordSpace n a) (y : WordSpace n b) :
    dotProduct (letterLift φ x) y = dotProduct x (fun w => y (φ ∘ w)) := by
  classical
  have hx : x = ∑ w, x w • Pi.single w (1 : ℂ) := by
    funext w
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_smul, letterLift_single]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext w
  simp [Pi.single_apply]

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_WordRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Relabel. -/

section

noncomputable section
namespace Saxl
open scoped TensorProduct

lemma altWord_relabel {n m d : ℕ} {α : Type*} (e : Fin n ≃ Fin m)
    (c : Fin n → α) (a : Fin n → Fin d) :
    relabelWord e (altWord (fiberGroup c) a) =
      altWord (fiberGroup (c ∘ e.symm)) (a ∘ e.symm) := by
  ext w
  exact altWord_fiber_relabel e.symm c a w

lemma relabelWord_letterLift {n m d D : ℕ} (e : Fin n ≃ Fin m) (f : Fin d → Fin D)
    (v : WordSpace n d) : relabelWord e (letterLift f v) = letterLift f (relabelWord e v) := by
  have hnm : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst m
  exact (Representation.IntertwiningMap.isIntertwining _ _ (letterLift f) e v).symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CandidateClearance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Clearance. -/

section

noncomputable section

namespace UniversalTensorSquare
open Saxl

lemma candidateBandRow_seed {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (rightWord (candidateCutPositions t)
      (rowWord (transposeTableau t) ∘ (candidateRotateRowPositions hM t : Equiv.Perm (Fin n))) i).val =
        (candidateRotateRow M b δ hM (candidateBandTableau t i)).val.2 := by
  simp only [rightWord, Function.comp_apply, rowWord, transposeTableau,
    candidateRotateRowPositions, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

lemma candidateBandCol_seed {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (rightWord (candidateCutPositions t)
      (rowWord t ∘ (candidateRotateColPositions hM t : Equiv.Perm (Fin n))) i).val =
        (candidateRotateCol M b δ hM (candidateBandTableau t i)).val.1 := by
  simp only [rightWord, Function.comp_apply, rowWord,
    candidateRotateColPositions, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CandidateShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Shuffle. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidateRotateRow_col (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    (candidateRotateRow M b δ hM x).val.2 =
      if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
        (if x.val.2 < M-2-x.val.1 then x.val.2+2
        else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)
      else (if x.val.2 < M-2-x.val.1 then x.val.2+2
        else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2) := rfl

lemma candidateRowShuffle_col (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    (candidateRowShuffle M b δ hM x).val.2 =
      if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
        (Equiv.swap (M+b-1) (M+b+δ-1) x.val.2) else x.val.2 := by
  change (if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
        (if x.val.1 = 0 then Equiv.swap (M+b-1) (M+b+δ-1) x.val.2 else x.val.2)
      else (if x.val.1 = 0 then Equiv.swap (M+b-1) (M+b+δ-1) x.val.2 else x.val.2)) = _
  split_ifs <;> rfl

private lemma separatedFirstRowNumber (M b δ j : ℕ) (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hj : M-2 ≤ j) (hj' : j < M+b+δ) :
    Equiv.swap (M-1) (M+b-1)
      (if Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j) < M-2 then
        Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)+2
      else if Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j) < M-2+2 then
        Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)-(M-2)
      else Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)) =
      if j = M-2 then 0 else if j = M+b+δ-1 then 1
      else if j < M+b-1 then j else j+1 := by
  have hs₀ : Equiv.swap (M-1) (M+b-1) (M-2) = M-2 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have ht₀ : Equiv.swap (M+b-1) (M+b+δ-1) (M-2) = M-2 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  by_cases hj₀ : j = M-2
  · subst j
    rw [ite_eq_left rfl, ht₀, hs₀, ite_eq_right (by omega), ite_eq_left (by omega), Nat.sub_self]
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  rw [ite_eq_right hj₀]
  by_cases hj₁ : j = M+b+δ-1
  · subst j
    rw [Equiv.swap_apply_right, Equiv.swap_apply_right, ite_eq_left rfl,
      ite_eq_right (by omega), ite_eq_left (by omega)]
    have he : M-1-(M-2) = 1 := by omega
    rw [he]
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  rw [ite_eq_right hj₁]
  let l := Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)
  have hl : M-2 ≤ l := by
    dsimp only [l]
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  have hl₀ : l ≠ M-2 := by
    intro he
    have he' := congrArg (fun z => Equiv.swap (M+b-1) (M+b+δ-1) (Equiv.swap (M-1) (M+b-1) z)) he
    simp only [l, Equiv.swap_apply_self, hs₀, ht₀] at he'
    exact hj₀ he'
  have hl₁ : l ≠ M-1 := by
    intro he
    have he' := congrArg (fun z => Equiv.swap (M+b-1) (M+b+δ-1) (Equiv.swap (M-1) (M+b-1) z)) he
    simp only [l, Equiv.swap_apply_self, Equiv.swap_apply_left] at he'
    exact hj₁ he'
  change Equiv.swap (M-1) (M+b-1) (if l < M-2 then l+2 else if l < M-2+2 then l-(M-2) else l) = _
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  dsimp only [l]
  rw [Equiv.swap_apply_self]
  by_cases he : j = M+b-1
  · subst j
    rw [Equiv.swap_apply_left, ite_eq_right (by omega)]
    omega
  · rw [Equiv.swap_apply_of_ne_of_ne he hj₁, ite_eq_left (by omega)]

lemma candidateSeparatedRow_band (M b δ : ℕ) (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (x : (candidate M b δ).cells) (hx : M-2 ≤ x.val.1+x.val.2) :
    (candidateSeparatedRow M b δ hM x).val.2 =
      if x.val.1 = 0 then
        if x.val.2 = M-2 then 0 else if x.val.2 = M+b+δ-1 then 1
        else if x.val.2 < M+b-1 then x.val.2 else x.val.2+1
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2 := by
  change (candidateRotateRow M b δ hM (candidateRowShuffle M b δ hM x)).val.2 = _
  rw [candidateRotateRow_col, candidateRowShuffle_row, candidateRowShuffle_col]
  have hm := mem_candidate.mp x.property
  rcases x with ⟨⟨i,j⟩,hm0⟩
  dsimp only at *
  by_cases hi : i = 0
  · subst i
    simp only [ite_true, if_true, Nat.sub_zero]
    exact separatedFirstRowNumber M b δ j hM hδ (by omega) (by omega)
  · simp only [hi, ite_false, if_false]
    rw [ite_eq_right (show ¬j < M-2-i by omega)]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Seeds. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidateBandRowShuffle_cell {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    candidateBandTableau t ((candidateBandRowShuffle hM t).val i) =
      candidateRowShuffle M b δ hM (candidateBandTableau t i) := by
  exact congrArg (fun x : candidateComplement M b δ => x.val)
    ((candidateComplementEquiv t).apply_symm_apply
      (candidateComplementRowShuffle M b δ hM (candidateComplementEquiv t i)))

lemma candidateBandRowSeed_val {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (candidateBandRowSeed hM t i).val =
      (candidateSeparatedRow M b δ hM (candidateBandTableau t i)).val.2 := by
  rw [candidateBandRowSeed, Function.comp_apply, candidateBandRow_seed,
    candidateBandRowShuffle_cell]
  rfl

lemma candidateBandColShuffle_cell {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    candidateBandTableau t ((candidateBandColShuffle hM t).val i) =
      candidateColShuffle M b δ hM (candidateBandTableau t i) := by
  exact congrArg (fun x : candidateComplement M b δ => x.val)
    ((candidateComplementEquiv t).apply_symm_apply
      (candidateComplementColShuffle M b δ hM (candidateComplementEquiv t i)))

lemma candidateBandColSeed_val {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (candidateBandColSeed hM t i).val =
      (candidateSeparatedRow M b δ hM (candidateSwap M b δ (candidateBandTableau t i))).val.2 := by
  rw [candidateBandColSeed, Function.comp_apply, candidateBandCol_seed,
    candidateBandColShuffle_cell]
  simp only [candidateRotateCol, candidateColShuffle, candidateSeparatedRow,
    Equiv.trans_apply]
  rfl

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Split. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidateBandParts_cell {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (x : Fin (2*M-1) ⊕ (Fin r ⊕ Fin r)) :
    (candidateBandTableau t ((candidateBandPartsEquiv hM t s₁ s₂).symm x)).val =
      (candidatePartsCell M b δ hM
        ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr s₁ s₂)) x)).val.val := by
  change ((candidateComplementEquiv t)
    (((candidateComplementEquiv t).symm)
      (candidatePartsCell M b δ hM _))).val.val = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma candidateBandSplit_path {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (q : Fin (2*M-1)) :
    (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm (Sum.inl q))).val =
      candidatePathCell M b δ q :=
  candidateBandParts_cell hM t s₁ s₂ (Sum.inl q)

lemma candidatePathCell_row_tag {M b δ : ℕ} (hM : 4 ≤ M)
    (i j : Fin (2*M-1)) :
    (candidatePathCell M b δ i).1 = (candidatePathCell M b δ j).1 ↔
      (i.val+1)/2 = (j.val+1)/2 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold candidatePathCell
  split_ifs <;> dsimp only <;> omega

lemma candidatePathCell_swap {M b δ : ℕ} (hM : 4 ≤ M)
    (i : Fin (2*M-1)) :
    (candidatePathCell M b δ i).swap = candidatePathCell M b δ i.rev := by
  have hi := i.isLt
  unfold candidatePathCell
  simp only [Fin.val_rev]
  split_ifs <;> simp only [Prod.swap_prod_mk, Prod.mk.injEq] <;> omega

lemma candidateSeparatedRow_path {M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (x : (candidate M b δ).cells) (q : Fin (2*M-1))
    (hx : x.val = candidatePathCell M b δ q) :
    (candidateSeparatedRow M b δ hM x).val.2 = if q.val = 0 then 0 else (q.val+1)%2 := by
  have hq := q.isLt
  rw [candidateSeparatedRow_band M b δ hM hδ x (by
    rw [hx]; exact (candidatePathCell_mem M b δ hM q).2), hx]
  unfold candidatePathCell
  split_ifs <;> dsimp only at * <;> omega

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandLetters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Letters. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma bandSmallLetter_injective {D : ℕ} (hD : 2 ≤ D) :
    Function.Injective (bandSmallLetter hD) := Fin.castLE_injective hD

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OddPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Odd Path. -/

section

noncomputable section
namespace Saxl.Band

lemma pathBasis_apply (i : Fin 4) : pathBasis i = conjugation (basis i.val) := by
  simp [pathBasis, matrixBasisEquiv, Pi.basisFun_apply,
    Pi.single_apply, conjugationEquiv]

end Saxl.Band

namespace Saxl.Columns

lemma chainFunctional_dualBlockWord (rs : List ℕ) (N : ℕ → Band.Mat) (p : ℕ) :
    Path.chainFunctional rs.sum p (dualBlockWord rs N) = segments p rs N := by
  rw [dualBlockWord, map_sum]
  simp_rw [map_smul, Path.chainFunctional_pure]
  exact sum_chain rs p N

theorem odd_path_ordered_contraction (r : ℕ) (rs : List ℕ)
    (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4) (hn : rs.sum = 2*r+1) :
    dotProduct
      (fun w : Fin (2*r+1) → Fin 4 =>
        dualBlockWord rs (fun i => Band.conjugation (Band.basis i))
          (w ∘ Fin.cast hn))
      (Path.bandWord r) ≠ 0 := by
  have h := Band.conjugation_blocks_ne_zero rs hrs
  rw [← Band.segments_conjugation rs 1,
    ← chainFunctional_dualBlockWord rs (fun i => Band.conjugation (Band.basis i)) 1] at h
  have hc : Path.chainFunctional (2*r+1) 1
      (fun w => dualBlockWord rs (fun i => Band.conjugation (Band.basis i))
        (w ∘ Fin.cast hn)) =
      Path.chainFunctional rs.sum 1
        (dualBlockWord rs (fun i => Band.conjugation (Band.basis i))) := by
    have aux : ∀ (m n : ℕ) (h : m = n) (x : WordSpace m 4),
        Path.chainFunctional n 1 (fun w => x (w ∘ Fin.cast h)) =
          Path.chainFunctional m 1 x := by
      intro m n h x
      subst n
      rfl
    exact aux _ _ hn _
  rw [← hc, Path.chainFunctional_endpoint] at h
  exact (mul_ne_zero_iff.mp h).2

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Path. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl
open scoped TensorProduct

lemma candidatePathRow_eq {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    candidatePathRow hM t s₁ s₂ =
      letterLift (bandSmallRowLetter hM)
        (relabelWord (candidatePathEquiv hM) (PathLayer.rowAlt (M-1))) := by
  unfold PathLayer.rowAlt
  rw [altWord_relabel, letterLift_altWord]
  unfold candidatePathRow
  congr 1
  · apply Subgroup.ext
    intro g
    change (∀ i, _ = _) ↔ (∀ i, _ = _)
    apply forall_congr'
    intro i
    simp only [candidateBandSplit_path]
    exact candidatePathCell_row_tag hM _ _
  · funext i
    apply Fin.ext
    rw [Function.comp_apply]
    change (candidateBandRowSeed hM t ((candidateBandSplit hM t s₁ s₂).symm (Sum.inl i))).val = _
    rw [candidateBandRowSeed_val, candidateSeparatedRow_path hM hδ _ i
      (candidateBandSplit_path hM t s₁ s₂ i)]
    simp only [bandSmallRowLetter, bandSmallLetter, Fin.val_castLE, Function.comp_apply,
      PathLayer.base, candidatePathEquiv, finCongr_symm, finCongr_apply, Fin.val_cast]
    split_ifs <;> rfl

lemma candidatePathCol_eq {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    candidatePathCol hM t s₁ s₂ =
      letterLift (bandSmallColLetter hM)
        (relabelWord ((Fin.revPerm).trans (candidatePathEquiv hM)) (PathLayer.rowAlt (M-1))) := by
  unfold PathLayer.rowAlt
  rw [altWord_relabel, letterLift_altWord]
  unfold candidatePathCol
  congr 1
  · apply Subgroup.ext
    intro g
    change (∀ i, _ = _) ↔ (∀ i, _ = _)
    apply forall_congr'
    intro i
    simp only [candidateBandSplit_path]
    have hh := candidatePathCell_row_tag (b := b) (δ := δ) hM (g i).rev i.rev
    rw [← candidatePathCell_swap hM, ← candidatePathCell_swap hM] at hh
    simpa only [Prod.fst_swap, Function.comp_apply, PathLayer.tag, Equiv.symm_trans,
      Equiv.trans_apply, candidatePathEquiv, finCongr_symm, finCongr_apply,
      Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev, Fin.val_cast,
      show 2*(M-1)+1 = 2*M-1 from by omega] using hh
  · funext i
    apply Fin.ext
    rw [Function.comp_apply]
    change (candidateBandColSeed hM t ((candidateBandSplit hM t s₁ s₂).symm (Sum.inl i))).val = _
    rw [candidateBandColSeed_val, candidateSeparatedRow_path hM hδ _ i.rev (by
      change (candidateBandTableau t _).val.swap = _
      rw [candidateBandSplit_path, candidatePathCell_swap hM])]
    simp only [bandSmallColLetter, bandSmallLetter, Fin.val_castLE, Function.comp_apply,
      PathLayer.base, candidatePathEquiv, Equiv.symm_trans, Equiv.trans_apply,
      finCongr_symm, finCongr_apply, Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_cast, Fin.val_rev,
      show 2*(M-1)+1 = 2*M-1 from by omega]
    split_ifs <;> rfl

lemma bandPairSmallLetter_injective {M b δ : ℕ} (hM : 4 ≤ M) :
    Function.Injective (@bandPairSmallLetter M b δ hM) :=
  pairLetterMap_injective _ _ (bandSmallLetter_injective _) (bandSmallLetter_injective _)

theorem candidatePathWord_eq {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    candidatePathWord hM t s₁ s₂ =
      (-1 : ℂ)^(M-1) • letterLift (bandPairSmallLetter hM)
        (relabelWord (candidatePathEquiv hM) (Path.bandWord (M-1))) := by
  rw [candidatePathWord, candidatePathRow_eq hM hδ, candidatePathCol_eq hM hδ,
    ← letterLift_wordTensor, ← map_smul, ← map_smul]
  congr 1
  ext w
  simp only [wordTensor_tmul, relabelWord_apply, Pi.smul_apply, smul_eq_mul]
  have hr : (splitRight w) ∘ (Fin.revPerm.trans (candidatePathEquiv hM)) =
      (fun i => (Path.parts ((w ∘ candidatePathEquiv hM) i)).2) ∘ Fin.rev := rfl
  rw [hr]
  exact PathLayer.paired_rowAlt (M-1) (w ∘ candidatePathEquiv hM)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_CommonPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common Path. -/

section

noncomputable section
namespace Saxl.Band

lemma extendFourBasis_pathBasis (i : ℕ) :
    extendFourBasis pathBasis i = conjugation (basis i) := by
  unfold extendFourBasis
  split_ifs with h
  · exact pathBasis_apply ⟨i,h⟩
  · rw [pathBasis_apply]
    congr 1
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ i by omega)
    simp [basis, Nat.add_comm]

theorem odd_path_common_basis :
    ∃ N : Module.Basis (Fin 4) ℂ Mat,
      ∀ (r : ℕ) (rs : List ℕ),
        (∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4) → ∀ hn : rs.sum = 2*r+1,
        dotProduct
          (fun w : Fin (2*r+1) → Fin 4 =>
            Columns.dualBlockWord rs (extendFourBasis N) (w ∘ Fin.cast hn))
          (Path.bandWord r) ≠ 0 := by
  refine ⟨pathBasis, ?_⟩
  intro r rs hrs hn
  rw [show extendFourBasis pathBasis = (fun i => conjugation (basis i)) from
    funext extendFourBasis_pathBasis]
  exact Columns.odd_path_ordered_contraction r rs hrs hn

end Saxl.Band
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_FlagDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flag Detection. -/

section

noncomputable section
namespace Saxl

lemma relabelWord_pair {n m d : ℕ} (e : Fin n ≃ Fin m)
    (x y : WordSpace n d) :
    dotProduct (relabelWord e x) (relabelWord e y) = dotProduct x y := by
  classical
  apply Fintype.sum_equiv ((Equiv.arrowCongr e (Equiv.refl _)).symm)
  intro w
  rfl

lemma relabelWord_symm_pair {n m d : ℕ} (e : Fin n ≃ Fin m)
    (x : WordSpace m d) (y : WordSpace n d) :
    dotProduct x (relabelWord e y) = dotProduct (relabelWord e.symm x) y := by
  conv_lhs => rw [← (relabelWord e).apply_symm_apply x]
  exact relabelWord_pair e _ _

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_BandContractions
attribute [-simp] _root_.OAI.Saxl.Balance.appendShortCells_left _root_.OAI.Saxl.Balance.appendShortCells_right _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Contractions. -/

section

noncomputable section
namespace Saxl

lemma relabelWord_trans {n m k d : ℕ} (e : Fin n ≃ Fin m) (f : Fin m ≃ Fin k)
    (v : WordSpace n d) : relabelWord f (relabelWord e v) = relabelWord (e.trans f) v := rfl

end Saxl
namespace Saxl.FlagColumns

lemma blocks_comp {a b : ℕ} (rs : List ℕ) (N : ℕ → Fin b → ℂ)
    (φ : Fin a → Fin b) (w : Fin rs.sum → Fin a) :
    blocks rs N (φ ∘ w) = blocks rs (fun i x => N i (φ x)) w := by
  simp only [blocks, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pure, Function.comp_apply]

lemma blocks_lift_relabel_pair {n a b : ℕ} (rs : List ℕ)
    (e : Fin rs.sum ≃ Fin n) (φ : Fin a → Fin b)
    (N : ℕ → Fin b → ℂ) (B : ℕ → Fin a → ℂ)
    (hN : ∀ i x, N i (φ x) = B i x) (v : WordSpace n a) :
    dotProduct (blocks rs N) (relabelWord e.symm (letterLift φ v)) =
      dotProduct (fun w => blocks rs B (w ∘ e)) v := by
  rw [relabelWord_symm_pair e.symm, Equiv.symm_symm,
    dotProduct_comm, letterLift_pair, dotProduct_comm]
  congr 1
  funext w
  change blocks rs N (φ ∘ (w ∘ e)) = _
  rw [blocks_comp, show (fun i x => N i (φ x)) = B from funext (fun i => funext (hN i))]

end Saxl.FlagColumns
namespace UniversalTensorSquare
open Saxl
open Saxl.FlagColumns

lemma bandPairSmallLetter_range {M b δ : ℕ} (hM : 4 ≤ M) (a) :
    candidatePathAlphabet M b δ a ↔ ∃ x, bandPairSmallLetter hM x = a := by
  constructor
  · intro ha
    refine ⟨finProdFinEquiv (⟨(finProdFinEquiv.symm a).1.val,ha.1⟩,
      ⟨(finProdFinEquiv.symm a).2.val,ha.2⟩), ?_⟩
    apply finProdFinEquiv.symm.injective
    simp only [bandPairSmallLetter, pairLetterMap, Equiv.symm_apply_apply,
      bandSmallRowLetter, bandSmallColLetter, bandSmallLetter]
    exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
  · rintro ⟨x,rfl⟩
    simp only [candidatePathAlphabet, bandPairSmallLetter, pairLetterMap,
      Equiv.symm_apply_apply, bandSmallRowLetter, bandSmallColLetter,
      bandSmallLetter, Fin.val_castLE]
    exact ⟨(finProdFinEquiv.symm x : Fin 2 × Fin 2).1.isLt,
      (finProdFinEquiv.symm x : Fin 2 × Fin 2).2.isLt⟩

theorem candidatePathWord_contraction_oai {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (rs : List ℕ) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4) (hn : rs.sum = 2*M-1) :
    ∃ N : ℕ → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) → ℂ,
      (∀ i a, ¬candidatePathAlphabet M b δ a → N i a = 0) ∧
      dotProduct (blocks rs N)
        (relabelWord (finCongr hn).symm (candidatePathWord hM t s₁ s₂)) ≠ 0 := by
  classical
  obtain ⟨B,hB⟩ := Band.odd_path_common_basis
  let C : ℕ → Fin 4 → ℂ := fun i a => Band.extendFourBasis B i
    (Path.parts a).1 (Path.parts a).2
  let N : ℕ → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) → ℂ :=
    fun i => Function.extend (bandPairSmallLetter hM) (C i) 0
  have hN : ∀ i a, N i (bandPairSmallLetter hM a) = C i a := fun i a =>
    (bandPairSmallLetter_injective hM).extend_apply (C i) 0 a
  refine ⟨N,?_,?_⟩
  · intro i a ha
    exact Function.extend_apply' (f := bandPairSmallLetter hM) (C i) (fun _ => 0) a ((bandPairSmallLetter_range hM a).not.mp ha)
  · rw [candidatePathWord_eq hM hδ, map_smul, dotProduct_smul, smul_eq_mul]
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    rw [relabelWord_letterLift, relabelWord_trans, ← relabelWord_letterLift]
    let e : Fin rs.sum ≃ Fin (2*(M-1)+1) := (finCongr hn).trans (candidatePathEquiv hM).symm
    change dotProduct (blocks rs N) (relabelWord e.symm (letterLift (bandPairSmallLetter hM)
      (Path.bandWord (M-1)))) ≠ 0
    rw [blocks_lift_relabel_pair rs e (bandPairSmallLetter hM) N C hN]
    have hraw : rs.sum = 2*(M-1)+1 := by omega
    convert hB (M-1) rs hrs hraw using 1
    all_goals try with_reducible_and_instances rfl
    congr 1

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.candidatePathWord_contraction_oai := @OAI.UniversalTensorSquare.candidatePathWord_contraction_oai
