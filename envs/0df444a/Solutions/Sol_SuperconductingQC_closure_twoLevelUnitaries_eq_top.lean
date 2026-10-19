-- Prove2me | solution 1 for SuperconductingQC.closure_twoLevelUnitaries_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:28:43.534986+00:00
-- url     : https://prove2.me/submissions/a68c6d68-b61d-4821-98cc-a524d31f8a09

import Mathlib
import Definitions.Def_SuperconductingQC_Gates

open scoped Matrix Kronecker

namespace SCTwo
open Matrix SuperconductingQC

set_option linter.unusedSectionVars false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def eAB (a b : ι) (hab : a ≠ b) : {x // x = a ∨ x = b} ≃ Fin 2 where
  toFun x := if x.1 = a then 0 else 1
  invFun i := if i = 0 then ⟨a, Or.inl rfl⟩ else ⟨b, Or.inr rfl⟩
  left_inv := by
    rintro ⟨x, rfl | rfl⟩
    · simp
    · simp [hab.symm]
  right_inv := by
    intro i; fin_cases i <;> simp [hab.symm]

def eqv (a b : ι) (hab : a ≠ b) : ι ≃ Fin 2 ⊕ {x // ¬ (x = a ∨ x = b)} :=
  (Equiv.sumCompl (fun x => x = a ∨ x = b)).symm.trans
    (Equiv.sumCongr (eAB a b hab) (Equiv.refl _))

variable (a b : ι) (hab : a ≠ b)

lemma eqv_a : eqv a b hab a = Sum.inl 0 := by
  simp [eqv, eAB, Equiv.sumCompl_symm_apply_of_pos]

lemma eqv_b : eqv a b hab b = Sum.inl 1 := by
  simp [eqv, eAB, Equiv.sumCompl_symm_apply_of_pos, hab.symm]

lemma eqv_other (x : ι) (hx : ¬ (x = a ∨ x = b)) : eqv a b hab x = Sum.inr ⟨x, hx⟩ := by
  simp [eqv, Equiv.sumCompl_symm_apply_of_neg, hx]

lemma eqv_symm_0 : (eqv a b hab).symm (Sum.inl 0) = a := by
  rw [Equiv.symm_apply_eq, eqv_a]

lemma eqv_symm_1 : (eqv a b hab).symm (Sum.inl 1) = b := by
  rw [Equiv.symm_apply_eq, eqv_b]

lemma eqv_symm_inr (c : {x // ¬ (x = a ∨ x = b)}) : (eqv a b hab).symm (Sum.inr c) = c.1 := by
  rw [Equiv.symm_apply_eq, eqv_other a b hab c.1 c.2]

lemma eqv_coe (c : {x // ¬ (x = a ∨ x = b)}) : eqv a b hab c.1 = Sum.inr c :=
  eqv_other a b hab c.1 c.2

noncomputable def embedM (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix ι ι ℂ :=
  (fromBlocks M 0 0 1).submatrix (eqv a b hab) (eqv a b hab)

lemma embedM_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    embedM a b hab M * embedM a b hab N = embedM a b hab (M * N) := by
  simp [embedM, submatrix_mul_equiv, fromBlocks_multiply]

lemma embedM_star (M : Matrix (Fin 2) (Fin 2) ℂ) :
    star (embedM a b hab M) = embedM a b hab (star M) := by
  simp [embedM, star_eq_conjTranspose, conjTranspose_submatrix, fromBlocks_conjTranspose]

lemma embedM_one : embedM a b hab (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  simp [embedM, fromBlocks_one, submatrix_one_equiv]

lemma embedM_unitary (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ unitaryGroup (Fin 2) ℂ) :
    embedM a b hab M ∈ unitaryGroup ι ℂ := by
  rw [mem_unitaryGroup_iff] at *
  rw [embedM_star, embedM_mul, hM, embedM_one]

lemma embedM_twoLevel (M : Matrix (Fin 2) (Fin 2) ℂ) : ∀ x y : ι,
    (x ≠ a ∧ x ≠ b) ∨ (y ≠ a ∧ y ≠ b) → embedM a b hab M x y = (1 : Matrix ι ι ℂ) x y := by
  intro x y h
  rcases h with ⟨hxa, hxb⟩ | ⟨hya, hyb⟩
  · have hx : ¬ (x = a ∨ x = b) := by tauto
    simp only [embedM, submatrix_apply, eqv_other a b hab x hx]
    by_cases hy : y = a ∨ y = b
    · rcases hy with rfl | rfl
      · simp [eqv_a, one_apply]; exact hxa
      · simp [eqv_b, one_apply]; exact hxb
    · simp [eqv_other a b hab y hy, one_apply]
  · have hy : ¬ (y = a ∨ y = b) := by tauto
    simp only [embedM, submatrix_apply, eqv_other a b hab y hy]
    by_cases hx : x = a ∨ x = b
    · rcases hx with rfl | rfl
      · simp [eqv_a, one_apply, hya.symm]
      · simp [eqv_b, one_apply, hyb.symm]
    · simp [eqv_other a b hab x hx, one_apply]

lemma embedM_mul_apply (M : Matrix (Fin 2) (Fin 2) ℂ) (U : Matrix ι ι ℂ) (x y : ι) :
    (embedM a b hab M * U) x y =
      if x = a then M 0 0 * U a y + M 0 1 * U b y
      else if x = b then M 1 0 * U a y + M 1 1 * U b y else U x y := by
  rw [mul_apply, ← (eqv a b hab).symm.sum_comp, Fintype.sum_sum_type]
  simp only [embedM, submatrix_apply, Equiv.apply_symm_apply, Fin.sum_univ_two, eqv_symm_0,
    eqv_symm_1, eqv_symm_inr, eqv_coe]
  split_ifs with h1 h2
  · subst h1; simp [eqv_a]
  · subst h2; simp [eqv_b]
  · have hx : ¬ (x = a ∨ x = b) := by tauto
    simp [eqv_other a b hab x hx, one_apply]


omit a b hab

lemma row_of_col (U : unitaryGroup ι ℂ) (a : ι)
    (h : ∀ x, (U : Matrix ι ι ℂ) x a = (1 : Matrix ι ι ℂ) x a) (y : ι) :
    (U : Matrix ι ι ℂ) a y = (1 : Matrix ι ι ℂ) a y := by
  have hU := congrFun (congrFun (mem_unitaryGroup_iff'.mp U.2) y) a
  rw [mul_apply, Finset.sum_eq_single a] at hU
  · rw [h a] at hU
    simp only [one_apply_eq, mul_one, star_apply] at hU
    have := congrArg star hU
    rw [star_star] at this
    rw [this]
    by_cases hya : y = a
    · subst hya; simp
    · simp [one_apply, hya, Ne.symm hya]
  · intro z _ hz; rw [h z]; simp [one_apply, hz]
  · simp

lemma col_norm (U : unitaryGroup ι ℂ) (a : ι)
    (h : ∀ x, x ≠ a → (U : Matrix ι ι ℂ) x a = 0) :
    star ((U : Matrix ι ι ℂ) a a) * (U : Matrix ι ι ℂ) a a = 1 := by
  have hU := congrFun (congrFun (mem_unitaryGroup_iff'.mp U.2) a) a
  rw [mul_apply, Finset.sum_eq_single a] at hU
  · simpa using hU
  · intro z _ hz; rw [h z hz]; simp
  · simp

theorem main : Subgroup.closure (twoLevelUnitaries ι) = ⊤ := by
  rw [eq_top_iff]
  intro U _
  have P : ∀ S : Finset ι, ∀ U : unitaryGroup ι ℂ,
      (∀ x y, (x ∉ S ∨ y ∉ S) → (U : Matrix ι ι ℂ) x y = (1 : Matrix ι ι ℂ) x y) →
      U ∈ Subgroup.closure (twoLevelUnitaries ι) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro U hU
      have : U = 1 := Subtype.ext (by ext x y; exact hU x y (Or.inl (Finset.notMem_empty x)))
      rw [this]; exact Subgroup.one_mem _
    | @insert a S' ha IH =>
      have Q : ∀ T : Finset ι, T ⊆ S' → ∀ U : unitaryGroup ι ℂ,
          (∀ x y, (x ∉ insert a S' ∨ y ∉ insert a S') →
            (U : Matrix ι ι ℂ) x y = (1 : Matrix ι ι ℂ) x y) →
          (∀ x, x ∉ insert a T → (U : Matrix ι ι ℂ) x a = 0) →
          U ∈ Subgroup.closure (twoLevelUnitaries ι) := by
        intro T
        induction T using Finset.induction_on with
        | empty =>
          intro _ U hU hcol
          have hcol' : ∀ x, x ≠ a → (U : Matrix ι ι ℂ) x a = 0 :=
            fun x hx => hcol x (by simpa using hx)
          have hc := col_norm U a hcol'
          set c := (U : Matrix ι ι ℂ) a a with hcdef
          let d : ι → ℂ := Function.update (fun _ => 1) a (star c)
          have hd : ∀ x, star (d x) * d x = 1 := by
            intro x
            by_cases hx : x = a
            · subst hx; simp only [d, Function.update_self, star_star]; rw [mul_comm]; exact hc
            · simp [d, Function.update_of_ne hx]
          have hD : diagonal d ∈ unitaryGroup ι ℂ := by
            rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose,
              diagonal_mul_diagonal]
            rw [← diagonal_one]; congr 1; funext x; exact hd x
          let D : unitaryGroup ι ℂ := ⟨diagonal d, hD⟩
          have hDmem : D ∈ Subgroup.closure (twoLevelUnitaries ι) := by
            apply Subgroup.subset_closure
            refine ⟨a, a, fun x y hxy => ?_⟩
            show diagonal d x y = _
            rw [diagonal_apply, one_apply]
            split_ifs with hxy'
            · subst hxy'
              have : x ≠ a := by tauto
              simp [d, Function.update_of_ne this]
            · rfl
          have hDU_apply : ∀ x y, ((D * U : unitaryGroup ι ℂ) : Matrix ι ι ℂ) x y =
              d x * (U : Matrix ι ι ℂ) x y := by
            intro x y
            show (diagonal d * (U : Matrix ι ι ℂ)) x y = _
            rw [diagonal_mul]
          have hcolDU : ∀ x, ((D * U : unitaryGroup ι ℂ) : Matrix ι ι ℂ) x a =
              (1 : Matrix ι ι ℂ) x a := by
            intro x
            rw [hDU_apply]
            by_cases hx : x = a
            · subst hx; simp only [d, Function.update_self, one_apply_eq]; exact hc
            · rw [hcol' x hx, one_apply_ne hx, mul_zero]
          have hDU : D * U ∈ Subgroup.closure (twoLevelUnitaries ι) := by
            apply IH
            intro x y hxy
            rcases hxy with hx | hy
            · by_cases hxa : x = a
              · subst hxa; exact row_of_col _ _ hcolDU y
              · have hx' : x ∉ insert a S' := by simp [hxa, hx]
                rw [hDU_apply, hU x y (Or.inl hx')]
                simp [d, Function.update_of_ne hxa]
            · by_cases hya : y = a
              · subst hya; exact hcolDU x
              · have hy' : y ∉ insert a S' := by simp [hya, hy]
                rw [hDU_apply, hU x y (Or.inr hy')]
                by_cases hxy : x = y
                · subst hxy; simp [d, Function.update_of_ne hya]
                · simp [one_apply_ne hxy]
          have : U = D⁻¹ * (D * U) := by group
          rw [this]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hDmem) hDU
        | @insert b T' hb IHT =>
          intro hsub U hU hcol
          have hbS : b ∈ S' := hsub (Finset.mem_insert_self _ _)
          have hab : a ≠ b := fun h => ha (h ▸ hbS)
          set α := (U : Matrix ι ι ℂ) a a with hα
          set β := (U : Matrix ι ι ℂ) b a with hβ
          by_cases hr : Complex.normSq α + Complex.normSq β = 0
          · apply IHT (subset_trans (Finset.subset_insert _ _) hsub) U hU
            intro x hx
            by_cases hxb : x = b
            · subst hxb
              have : Complex.normSq β = 0 := by
                linarith [Complex.normSq_nonneg α, Complex.normSq_nonneg β]
              exact Complex.normSq_eq_zero.mp this
            · apply hcol; simp only [Finset.mem_insert, not_or] at hx ⊢; tauto
          · have hpos : 0 < Complex.normSq α + Complex.normSq β :=
              lt_of_le_of_ne (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (Ne.symm hr)
            set s := Real.sqrt (Complex.normSq α + Complex.normSq β) with hs
            have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
            have hs2 : s * s = Complex.normSq α + Complex.normSq β :=
              Real.mul_self_sqrt hpos.le
            have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
            let M : Matrix (Fin 2) (Fin 2) ℂ :=
              !![star α / s, star β / s; -β / s, α / s]
            have hM : M ∈ unitaryGroup (Fin 2) ℂ := by
              have hsC2 : (s : ℂ) * s = α * star α + β * star β := by
                have := congrArg (fun t : ℝ => (t : ℂ)) hs2
                simp only [Complex.ofReal_mul, Complex.ofReal_add] at this
                rw [this]; simp only [Complex.star_def, Complex.mul_conj]
              rw [mem_unitaryGroup_iff']
              ext i j
              fin_cases i <;> fin_cases j <;>
                simp [M, star_eq_conjTranspose, mul_apply, Fin.sum_univ_two,
                  Complex.conj_ofReal] <;> field_simp <;>
                simp only [Complex.star_def] at hsC2 ⊢ <;> first | ring1 | (rw [sq, hsC2]; ring1)
            let G : unitaryGroup ι ℂ := ⟨embedM a b hab M, embedM_unitary a b hab M hM⟩
            have hG : G ∈ Subgroup.closure (twoLevelUnitaries ι) :=
              Subgroup.subset_closure ⟨a, b, embedM_twoLevel a b hab M⟩
            have hGU_apply : ∀ x y, ((G * U : unitaryGroup ι ℂ) : Matrix ι ι ℂ) x y =
                if x = a then M 0 0 * (U : Matrix ι ι ℂ) a y + M 0 1 * (U : Matrix ι ι ℂ) b y
                else if x = b then M 1 0 * (U : Matrix ι ι ℂ) a y + M 1 1 * (U : Matrix ι ι ℂ) b y
                else (U : Matrix ι ι ℂ) x y := fun x y => embedM_mul_apply a b hab M _ x y
            have hGU : G * U ∈ Subgroup.closure (twoLevelUnitaries ι) := by
              apply IHT (subset_trans (Finset.subset_insert _ _) hsub)
              · intro x y hxy
                rw [hGU_apply]
                rcases hxy with hx | hy
                · have hxa : x ≠ a := fun h => hx (h ▸ Finset.mem_insert_self _ _)
                  have hxb : x ≠ b := fun h => hx (h ▸ Finset.mem_insert_of_mem hbS)
                  rw [if_neg hxa, if_neg hxb, hU x y (Or.inl hx)]
                · have hya : a ≠ y := fun h => hy (h ▸ Finset.mem_insert_self _ _)
                  have hyb : b ≠ y := fun h => hy (h ▸ Finset.mem_insert_of_mem hbS)
                  have h1 : (U : Matrix ι ι ℂ) a y = 0 := by
                    rw [hU a y (Or.inr hy), one_apply_ne hya]
                  have h2 : (U : Matrix ι ι ℂ) b y = 0 := by
                    rw [hU b y (Or.inr hy), one_apply_ne hyb]
                  split_ifs with hxa hxb
                  · subst hxa; rw [h1, h2, one_apply_ne hya]; ring
                  · subst hxb; rw [h1, h2, one_apply_ne hyb]; ring
                  · exact hU x y (Or.inr hy)
              · intro x hx
                rw [hGU_apply]
                have hxa : x ≠ a := fun h => hx (h ▸ Finset.mem_insert_self _ _)
                rw [if_neg hxa]
                split_ifs with hxb
                · simp only [M, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
                    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
                  rw [← hα, ← hβ]; field_simp; ring
                · apply hcol; simp only [Finset.mem_insert, not_or] at hx ⊢; tauto
            have : U = G⁻¹ * (G * U) := by group
            rw [this]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hG) hGU
      intro U hU
      apply Q S' subset_rfl U hU
      intro x hx
      rw [hU x a (Or.inl hx), one_apply_ne]
      rintro rfl; exact hx (Finset.mem_insert_self _ _)
  exact P Finset.univ U (fun x y h => by simp at h)

end SCTwo

open SuperconductingQC in
theorem solution (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Subgroup.closure (twoLevelUnitaries ι) = ⊤ :=
  SCTwo.main
