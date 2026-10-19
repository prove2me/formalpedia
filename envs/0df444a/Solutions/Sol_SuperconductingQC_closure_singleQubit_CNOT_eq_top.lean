-- Prove2me | solution 1 for SuperconductingQC.closure_singleQubit_CNOT_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:01:16.216198+00:00
-- url     : https://prove2.me/submissions/39b338f9-11c8-455c-954a-562e0ccdf885

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


open scoped Matrix Kronecker

namespace SCTwo
open Matrix SuperconductingQC

set_option linter.unusedSectionVars false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mainK (K : Subgroup (unitaryGroup ι ℂ))
    (hDK : ∀ (a : ι) (z : ℂ) (h : diagonal (Function.update (fun _ => (1 : ℂ)) a z) ∈ unitaryGroup ι ℂ),
      star z * z = 1 → (⟨_, h⟩ : unitaryGroup ι ℂ) ∈ K)
    (hEK : ∀ (a b : ι) (hab : a ≠ b) (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ unitaryGroup (Fin 2) ℂ),
      (⟨embedM a b hab M, embedM_unitary a b hab M hM⟩ : unitaryGroup ι ℂ) ∈ K) : K = ⊤ := by
  rw [eq_top_iff]
  intro U _
  have P : ∀ S : Finset ι, ∀ U : unitaryGroup ι ℂ,
      (∀ x y, (x ∉ S ∨ y ∉ S) → (U : Matrix ι ι ℂ) x y = (1 : Matrix ι ι ℂ) x y) →
      U ∈ K := by
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
          U ∈ K := by
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
          have hDmem : D ∈ K := hDK a (star c) hD (by rw [star_star, mul_comm]; exact hc)
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
          have hDU : D * U ∈ K := by
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
            have hG : G ∈ K := hEK a b hab M hM
            have hGU_apply : ∀ x y, ((G * U : unitaryGroup ι ℂ) : Matrix ι ι ℂ) x y =
                if x = a then M 0 0 * (U : Matrix ι ι ℂ) a y + M 0 1 * (U : Matrix ι ι ℂ) b y
                else if x = b then M 1 0 * (U : Matrix ι ι ℂ) a y + M 1 1 * (U : Matrix ι ι ℂ) b y
                else (U : Matrix ι ι ℂ) x y := fun x y => embedM_mul_apply a b hab M _ x y
            have hGU : G * U ∈ K := by
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


open scoped Matrix Kronecker

namespace SCU
open Matrix SuperconductingQC

set_option linter.unusedSectionVars false

variable {n : ℕ}

abbrev N (n : ℕ) := Fin n → Fin 2

abbrev GG (n : ℕ) := Subgroup.closure (singleQubitGates n ∪ twoQubitGateInstances n CNOT)

def InG (A : Matrix (N n) (N n) ℂ) : Prop := ∃ W ∈ GG n, (W : Matrix (N n) (N n) ℂ) = A

lemma InG.mul {A B : Matrix (N n) (N n) ℂ} (hA : InG A) (hB : InG B) : InG (A * B) := by
  obtain ⟨W, hW, rfl⟩ := hA
  obtain ⟨V, hV, rfl⟩ := hB
  exact ⟨W * V, Subgroup.mul_mem _ hW hV, rfl⟩

lemma InG.onQubit (k : Fin n) (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ unitaryGroup (Fin 2) ℂ)
    (h : SuperconductingQC.onQubit k U ∈ unitaryGroup (N n) ℂ) : InG (SuperconductingQC.onQubit k U) :=
  ⟨⟨_, h⟩, Subgroup.subset_closure (Or.inl ⟨k, U, hU, rfl⟩), rfl⟩

lemma InG.onPair (i j : Fin n) (hij : i ≠ j)
    (h : onPair i j CNOT ∈ unitaryGroup (N n) ℂ) : InG (onPair i j CNOT) :=
  ⟨⟨_, h⟩, Subgroup.subset_closure (Or.inr ⟨i, j, hij, rfl⟩), rfl⟩

/-- generic operator acting on qubit `k` with a matrix depending on the other qubits -/
def Op (k : Fin n) (F : N n → Matrix (Fin 2) (Fin 2) ℂ) : Matrix (N n) (N n) ℂ := fun x y =>
  if ∀ j, j ≠ k → x j = y j then F x (x k) (y k) else 0

def Local (k : Fin n) (F : N n → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ x b, F (Function.update x k b) = F x

lemma agree_iff (k : Fin n) (x y : N n) :
    (∀ j, j ≠ k → x j = y j) ↔ y = Function.update x k (y k) := by
  constructor
  · intro h; funext j; by_cases hj : j = k
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact (h j hj).symm
  · intro h j hj; rw [h, Function.update_of_ne hj]

lemma Local.eq {k : Fin n} {F : N n → Matrix (Fin 2) (Fin 2) ℂ} (hF : Local k F) {x y : N n}
    (h : ∀ j, j ≠ k → x j = y j) : F y = F x := by
  rw [(agree_iff k x y).mp h, hF]

lemma sum_off {M : Type*} [AddCommMonoid M] (k : Fin n) (x : N n) (f : N n → M)
    (hf : ∀ z, ¬ (∀ j, j ≠ k → x j = z j) → f z = 0) :
    ∑ z, f z = ∑ b : Fin 2, f (Function.update x k b) := by
  have hinj : Function.Injective (fun b : Fin 2 => Function.update x k b) := by
    intro b b' h; have := congrFun h k; simpa using this
  rw [← Finset.sum_image (fun b _ b' _ h => hinj h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro z _ hz
  apply hf
  intro h
  apply hz
  rw [Finset.mem_image]
  exact ⟨z k, Finset.mem_univ _, ((agree_iff k x z).mp h).symm⟩

lemma Op_mul (k : Fin n) (F G : N n → Matrix (Fin 2) (Fin 2) ℂ) (hG : Local k G) :
    Op k F * Op k G = Op k (fun x => F x * G x) := by
  ext x y
  rw [mul_apply, sum_off k x]
  · have key : ∀ b : Fin 2, Op k F x (Function.update x k b) * Op k G (Function.update x k b) y =
        F x (x k) b * (if ∀ j, j ≠ k → x j = y j then G x b (y k) else 0) := by
      intro b
      have h1 : ∀ j, j ≠ k → x j = Function.update x k b j :=
        fun j hj => (Function.update_of_ne hj _ _).symm
      have e1 : Op k F x (Function.update x k b) = F x (x k) b := by
        unfold Op; rw [if_pos h1, Function.update_self]
      have e2 : Op k G (Function.update x k b) y =
          if (∀ j, j ≠ k → x j = y j) then G x b (y k) else 0 := by
        unfold Op; rw [hG, Function.update_self]
        congr 1; apply propext; constructor
        · intro h j hj; rw [← h j hj, Function.update_of_ne hj]
        · intro h j hj; rw [Function.update_of_ne hj]; exact h j hj
      rw [e1, e2]
    rw [Finset.sum_congr rfl (fun b _ => key b)]
    by_cases hxy : ∀ j, j ≠ k → x j = y j
    · simp only [if_pos hxy, Op, mul_apply]
    · simp only [if_neg hxy, Op, mul_zero, Finset.sum_const_zero]
  · intro z hz; simp [Op, hz]

lemma Op_one (k : Fin n) : Op k (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext x y
  simp only [Op, one_apply]
  by_cases h : ∀ j, j ≠ k → x j = y j
  · rw [if_pos h]
    by_cases hk : x k = y k
    · have hxy : x = y := by
        funext j; by_cases hj : j = k
        · subst hj; exact hk
        · exact h j hj
      rw [if_pos hk, if_pos hxy]
    · rw [if_neg hk, if_neg]; intro hxy; exact hk (congrFun hxy k)
  · rw [if_neg h, if_neg]; rintro rfl; exact h fun _ _ => rfl

lemma Op_star (k : Fin n) (F : N n → Matrix (Fin 2) (Fin 2) ℂ) (hF : Local k F) :
    star (Op k F) = Op k (fun x => star (F x)) := by
  ext x y
  simp only [star_apply, Op]
  by_cases h : ∀ j, j ≠ k → x j = y j
  · have h' : ∀ j, j ≠ k → y j = x j := fun j hj => (h j hj).symm
    rw [if_pos h', if_pos h, hF.eq h]
  · have h' : ¬ ∀ j, j ≠ k → y j = x j := fun h' => h fun j hj => (h' j hj).symm
    rw [if_neg h', if_neg h, star_zero]

lemma Op_unitary (k : Fin n) (F : N n → Matrix (Fin 2) (Fin 2) ℂ) (hF : Local k F)
    (hU : ∀ x, F x ∈ unitaryGroup (Fin 2) ℂ) : Op k F ∈ unitaryGroup (N n) ℂ := by
  rw [mem_unitaryGroup_iff', Op_star k F hF, Op_mul k _ _ hF, ← Op_one k]
  congr 1; funext x; exact mem_unitaryGroup_iff'.mp (hU x)

lemma onQubit_eq (k : Fin n) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    SuperconductingQC.onQubit k U = Op k (fun _ => U) := rfl

lemma InG.onQubit' (k : Fin n) (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ unitaryGroup (Fin 2) ℂ) :
    InG (Op k (fun _ => U)) :=
  InG.onQubit k U hU (Op_unitary k _ (fun _ _ => rfl) (fun _ => hU))

lemma Op_diag (k : Fin n) (g : N n → Fin 2 → ℂ) :
    Op k (fun x => diagonal (g x)) = diagonal (fun x => g x (x k)) := by
  ext x y
  simp only [Op, diagonal_apply]
  by_cases h : ∀ j, j ≠ k → x j = y j
  · rw [if_pos h]
    by_cases hk : x k = y k
    · rw [if_pos hk, if_pos]; funext j; by_cases hj : j = k
      · subst hj; exact hk
      · exact h j hj
    · rw [if_neg hk, if_neg]; intro hxy; exact hk (congrFun hxy k)
  · rw [if_neg h, if_neg]; rintro rfl; exact h fun _ _ => rfl

/-! permutation matrices -/
def Pm (f : N n → N n) : Matrix (N n) (N n) ℂ := fun x y => if x = f y then 1 else 0

lemma Pm_conj_apply (f : N n → N n) (hf : ∀ y, f (f y) = y) (A : Matrix (N n) (N n) ℂ) (x y : N n) :
    (Pm f * A * Pm f) x y = A (f x) (f y) := by
  rw [mul_apply, Finset.sum_eq_single (f y)]
  · rw [mul_apply, Finset.sum_eq_single (f x)]
    · simp [Pm, hf]
    · intro z _ hz; simp only [Pm]; rw [if_neg]; · simp
      rintro rfl; exact hz (hf z).symm
    · simp
  · intro z _ hz; simp [Pm, hz]
  · simp

lemma Pm_conj_diag (f : N n → N n) (hf : ∀ y, f (f y) = y) (d : N n → ℂ) :
    Pm f * diagonal d * Pm f = diagonal (fun x => d (f x)) := by
  ext x y
  rw [Pm_conj_apply f hf, diagonal_apply, diagonal_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg, if_neg h]; intro h'; apply h; rw [← hf x, h', hf]

lemma Pm_conj_Op (f : N n → N n) (hf : ∀ y, f (f y) = y) (k : Fin n)
    (hk : ∀ x b, f (Function.update x k b) = Function.update (f x) k b)
    (F : N n → Matrix (Fin 2) (Fin 2) ℂ) :
    Pm f * Op k F * Pm f = Op k (fun x => F (f x)) := by
  have hfk : ∀ x, f x k = x k := by
    intro x
    have := congrFun (hk x (x k)) k
    simp only [Function.update_self, Function.update_eq_self] at this
    exact this
  have hag : ∀ x y, (∀ j, j ≠ k → x j = y j) → (∀ j, j ≠ k → f x j = f y j) := by
    intro x y h
    have hy := (agree_iff k x y).mp h
    rw [agree_iff, hfk]
    conv_lhs => rw [hy]
    exact hk x (y k)
  ext x y
  rw [Pm_conj_apply f hf]
  simp only [Op, hfk]
  by_cases h : ∀ j, j ≠ k → x j = y j
  · rw [if_pos (hag x y h), if_pos h]
  · rw [if_neg, if_neg h]
    intro h'; apply h
    have := hag _ _ h'
    simpa [hf] using this

lemma Pm_unitary (f : N n → N n) (hf : ∀ y, f (f y) = y) : Pm f ∈ unitaryGroup (N n) ℂ := by
  rw [mem_unitaryGroup_iff']
  have hs : star (Pm f) = Pm f := by
    ext x y
    simp only [star_apply, Pm]
    have : (y = f x) ↔ (x = f y) := ⟨fun h => by rw [h, hf], fun h => by rw [h, hf]⟩
    by_cases h : x = f y
    · rw [if_pos (this.mpr h), if_pos h]; simp
    · rw [if_neg (fun h' => h (this.mp h')), if_neg h]; simp
  rw [hs]
  have := Pm_conj_diag f hf (fun _ => 1)
  rw [diagonal_one, mul_one] at this
  rw [this]

end SCU


open scoped Matrix

namespace SCU2
open Matrix

lemma unit_sqrt (z : ℂ) (hz : star z * z = 1) : ∃ s : ℂ, s * s = z ∧ star s * s = 1 := by
  have hn : ‖z‖ = 1 := by
    have h1 : (Complex.normSq z : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]; exact hz
    have h2 : Complex.normSq z = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg z]
  refine ⟨Complex.exp (↑(Complex.arg z / 2) * Complex.I), ?_, ?_⟩
  · rw [← Complex.exp_add]
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hn, Complex.ofReal_one, one_mul] at this
    rw [show (↑(Complex.arg z / 2) * Complex.I + ↑(Complex.arg z / 2) * Complex.I : ℂ) =
      ↑(Complex.arg z) * Complex.I by push_cast; ring]
    exact this
  · rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    ring_nf; exact Complex.exp_zero

lemma diag2 (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ unitaryGroup (Fin 2) ℂ) :
    ∃ W ∈ unitaryGroup (Fin 2) ℂ, ∃ l m : ℂ, star l * l = 1 ∧ star m * m = 1 ∧
      U = W * diagonal ![l, m] * star W := by
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (Matrix.toLin' U)
  obtain ⟨v, hv, hv0⟩ := hl.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv
  have hpos : 0 < Complex.normSq (v 0) + Complex.normSq (v 1) := by
    by_contra h
    push Not at h
    have h0 : Complex.normSq (v 0) = 0 := by linarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
    have h1 : Complex.normSq (v 1) = 0 := by linarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
    apply hv0; funext i; fin_cases i
    · exact Complex.normSq_eq_zero.mp h0
    · exact Complex.normSq_eq_zero.mp h1
  set r := Real.sqrt (Complex.normSq (v 0) + Complex.normSq (v 1)) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
  have hr2 : r * r = Complex.normSq (v 0) + Complex.normSq (v 1) := Real.mul_self_sqrt hpos.le
  set u : Fin 2 → ℂ := ((r : ℂ)⁻¹) • v with hu
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hun : star (u 0) * u 0 + star (u 1) * u 1 = 1 := by
    simp only [hu, Pi.smul_apply, smul_eq_mul, star_mul', star_inv₀, Complex.star_def,
      Complex.conj_ofReal]
    have : (starRingEnd ℂ) (v 0) * v 0 + (starRingEnd ℂ) (v 1) * v 1 = (r : ℂ) * r := by
      rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast hr2.symm
    field_simp
    linear_combination this
  have huv : U *ᵥ u = l • u := by
    rw [hu, Matrix.mulVec_smul, hv, smul_comm]
  set W : Matrix (Fin 2) (Fin 2) ℂ := !![u 0, -star (u 1); u 1, star (u 0)] with hW
  have hWu : W ∈ unitaryGroup (Fin 2) ℂ := by
    rw [mem_unitaryGroup_iff']
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hW, mul_apply, Fin.sum_univ_two, star_apply, Complex.star_def] <;>
      simp only [Complex.star_def] at hun <;>
      first | ring1 | linear_combination hun | linear_combination (-1 : ℂ) * hun
  set M := star W * U * W with hM
  have hMu : M ∈ unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hWu) hU) hWu
  have hcol : ∀ j, (U * W) j 0 = l * u j := by
    intro j
    have := congrFun huv j
    simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    simp only [mul_apply, Fin.sum_univ_two, hW]
    simpa using this
  have hMcol : ∀ i, M i 0 = ∑ j, star (W j i) * (l * u j) := by
    intro i
    rw [hM, Matrix.mul_assoc, mul_apply]
    simp only [hcol, star_apply]
  have hM00 : M 0 0 = l := by
    rw [hMcol]; simp only [Fin.sum_univ_two, hW]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination l * hun
  have hM10 : M 1 0 = 0 := by
    rw [hMcol]; simp only [Fin.sum_univ_two, hW]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, star_neg, star_star]
    ring
  have hMM := mem_unitaryGroup_iff'.mp hMu
  have e : ∀ i j, ∑ k, star (M k i) * M k j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    intro i j; rw [← hMM]; simp [mul_apply, star_apply]
  have e00 := e 0 0
  have e01 := e 0 1
  have e11 := e 1 1
  simp only [Fin.sum_univ_two, hM00, hM10, star_zero, zero_mul, add_zero, one_apply_eq,
    one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at e00 e01 e11
  have hl0 : star l ≠ 0 := by intro h; rw [h, zero_mul] at e00; exact zero_ne_one e00
  have hM01 : M 0 1 = 0 := (mul_eq_zero.mp e01).resolve_left hl0
  rw [hM01, star_zero, zero_mul, zero_add] at e11
  refine ⟨W, hWu, l, M 1 1, e00, e11, ?_⟩
  have hMd : M = diagonal ![l, M 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hM00, hM10, hM01]
  rw [← hMd, hM]
  have hWW := mem_unitaryGroup_iff.mp hWu
  calc U = (W * star W) * U * (W * star W) := by rw [hWW, one_mul, mul_one]
    _ = W * (star W * U * W) * star W := by simp only [Matrix.mul_assoc]

lemma unitary_sqrt (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ unitaryGroup (Fin 2) ℂ) :
    ∃ V ∈ unitaryGroup (Fin 2) ℂ, V * V = U := by
  obtain ⟨W, hW, l, m, hl, hm, rfl⟩ := diag2 U hU
  obtain ⟨a, ha, ha'⟩ := unit_sqrt l hl
  obtain ⟨b, hb, hb'⟩ := unit_sqrt m hm
  have hD : diagonal ![a, b] ∈ unitaryGroup (Fin 2) ℂ := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1; funext i; fin_cases i
    · exact ha'
    · exact hb'
  refine ⟨W * diagonal ![a, b] * star W,
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hW hD) (Unitary.star_mem hW), ?_⟩
  have hWW := mem_unitaryGroup_iff'.mp hW
  calc W * diagonal ![a, b] * star W * (W * diagonal ![a, b] * star W)
      = W * diagonal ![a, b] * (star W * W) * diagonal ![a, b] * star W := by
        simp only [Matrix.mul_assoc]
    _ = W * diagonal ![l, m] * star W := by
        rw [hWW, Matrix.mul_one, Matrix.mul_assoc W (diagonal _) (diagonal _), diagonal_mul_diagonal]
        have : (fun i => ![a, b] i * ![a, b] i) = ![l, m] := by
          funext i; fin_cases i
          · exact ha
          · exact hb
        rw [this]

end SCU2


open scoped Matrix Kronecker

namespace SCU
open Matrix SuperconductingQC

set_option linter.unusedSectionVars false
variable {n : ℕ}

def Xm : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

lemma Xm_unitary : Xm ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff']
  ext i j; fin_cases i <;> fin_cases j <;> simp [Xm, mul_apply, Fin.sum_univ_two, star_apply]

lemma fin2_ne_one : ∀ t : Fin 2, ¬ t = 1 → t = 0 := by decide

/-- flip bit `k` when `p` holds -/
def flipIf (k : Fin n) (p : N n → Prop) [DecidablePred p] (x : N n) : N n :=
  if p x then Function.update x k (x k + 1) else x

lemma flipIf_invol (k : Fin n) (p : N n → Prop) [DecidablePred p]
    (hp : ∀ x b, p (Function.update x k b) ↔ p x) (x : N n) : flipIf k p (flipIf k p x) = x := by
  unfold flipIf
  by_cases h : p x
  · have h' : p (Function.update x k (x k + 1)) := (hp x _).mpr h
    rw [if_pos h, if_pos h']
    funext j; by_cases hj : j = k
    · subst hj; simp only [Function.update_self]
      generalize x j = t; fin_cases t <;> decide
    · simp [Function.update_of_ne hj]
  · rw [if_neg h, if_neg h]

lemma Op_flip (k : Fin n) (p : N n → Prop) [DecidablePred p]
    (hp : ∀ x b, p (Function.update x k b) ↔ p x) :
    Op k (fun x => if p x then Xm else 1) = Pm (flipIf k p) := by
  ext x y
  simp only [Op, Pm]
  by_cases h : ∀ j, j ≠ k → x j = y j
  · rw [if_pos h]
    have hy := (agree_iff k x y).mp h
    have hpxy : p y ↔ p x := by rw [hy]; exact hp x _
    by_cases hpx : p x
    · have hf : flipIf k p y = Function.update y k (y k + 1) := if_pos (hpxy.mpr hpx)
      rw [if_pos hpx, hf]
      have : (x = Function.update y k (y k + 1)) ↔ x k = y k + 1 := by
        constructor
        · intro e; rw [e]; simp
        · intro e; funext j; by_cases hj : j = k
          · subst hj; simp [e]
          · rw [Function.update_of_ne hj]; exact h j hj
      simp only [this]
      generalize x k = a; generalize y k = b
      fin_cases a <;> fin_cases b <;> simp [Xm] <;> decide
    · have hf : flipIf k p y = y := if_neg (fun h' => hpx (hpxy.mp h'))
      rw [if_neg hpx, hf]
      have : (x = y) ↔ x k = y k := by
        constructor
        · intro e; rw [e]
        · intro e; funext j; by_cases hj : j = k
          · subst hj; exact e
          · exact h j hj
      simp only [this, one_apply]
  · rw [if_neg h, if_neg]
    intro e; apply h; intro j hj; rw [e]; unfold flipIf; split_ifs
    · rw [Function.update_of_ne hj]
    · rfl

lemma onPair_CNOT_eq (c k : Fin n) (hck : c ≠ k) :
    onPair c k CNOT = Op k (fun x => if x c = 1 then Xm else 1) := by
  rw [Op_flip k (fun x => x c = 1) (fun x b => by rw [Function.update_of_ne hck])]
  ext x y
  simp only [onPair, CNOT, Pm]
  have key : ((∀ l, l ≠ c → l ≠ k → x l = y l) ∧ (x c = y c ∧ x k = y k + y c)) ↔
      x = flipIf k (fun x => x c = 1) y := by
    unfold flipIf
    constructor
    · rintro ⟨h, hc, hk⟩
      funext l
      by_cases hl : l = k
      · subst hl
        split_ifs with h1
        · simp [hk, h1]
        · have : y c = 0 := fin2_ne_one _ h1
          simp [hk, this]
      · have : x l = y l := by
          by_cases hl' : l = c
          · subst hl'; exact hc
          · exact h l hl' hl
        split_ifs <;> simp [Function.update_of_ne hl, this]
    · intro e
      have hc : x c = y c := by rw [e]; split_ifs <;> simp [Function.update_of_ne hck]
      refine ⟨fun l hlc hlk => ?_, hc, ?_⟩
      · rw [e]; split_ifs <;> simp [Function.update_of_ne hlk]
      · rw [e]; split_ifs with h1
        · simp [h1]
        · have : y c = 0 := fin2_ne_one _ h1
          simp [this]
  by_cases h1 : ∀ l, l ≠ c → l ≠ k → x l = y l
  · rw [if_pos h1]
    by_cases h2 : x c = y c ∧ x k = y k + y c
    · rw [if_pos h2, if_pos (key.mp ⟨h1, h2⟩)]
    · rw [if_neg h2, if_neg (fun h => h2 (key.mpr h).2)]
  · rw [if_neg h1, if_neg (fun h => h1 (key.mpr h).1)]

lemma InG.cnot (c k : Fin n) (hck : c ≠ k) : InG (Op k (fun x => if x c = 1 then Xm else 1)) := by
  rw [← onPair_CNOT_eq c k hck]
  apply InG.onPair c k hck
  rw [onPair_CNOT_eq c k hck]
  exact Op_unitary k _ (fun x b => by simp only [Function.update_of_ne hck])
    (fun x => by split_ifs; exact Xm_unitary; exact one_mem _)

lemma diag_unit (z : ℂ) (hz : star z * z = 1) : diagonal ![1, z] ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1; funext i; fin_cases i
  · simp
  · exact hz

lemma Op_const_diag (k : Fin n) (z : ℂ) :
    Op k (fun _ => diagonal ![1, z]) = diagonal (fun x => ![1, z] (x k)) :=
  Op_diag k (fun _ => ![1, z])

lemma InG.diag1 (k : Fin n) (z : ℂ) (hz : star z * z = 1) :
    InG (diagonal (fun x : N n => ![1, z] (x k))) := by
  rw [← Op_const_diag]; exact InG.onQubit' k _ (diag_unit z hz)

lemma flip_local (c k : Fin n) (hck : c ≠ k) :
    ∀ (x : N n) b, (fun x : N n => x c = 1) (Function.update x k b) ↔ (fun x : N n => x c = 1) x :=
  fun x b => by simp only [Function.update_of_ne hck]

lemma InG.Pflip (c k : Fin n) (hck : c ≠ k) : InG (Pm (flipIf k (fun x : N n => x c = 1))) := by
  rw [← Op_flip k _ (flip_local c k hck)]; exact InG.cnot c k hck

lemma ctrl_local (c k : Fin n) (hck : c ≠ k) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Local k (fun x : N n => if x c = 1 then A else B) :=
  fun x b => by simp only [Function.update_of_ne hck]

lemma InG.ctrlDiag (c k : Fin n) (hck : c ≠ k) (l m : ℂ) (hl : star l * l = 1)
    (hm : star m * m = 1) :
    InG (Op k (fun x : N n => if x c = 1 then diagonal ![l, m] else 1)) := by
  obtain ⟨β, hβ, hβu⟩ := SCU2.unit_sqrt (star l * m)
    (by rw [star_mul', star_star]; linear_combination (star m * m) * hl + hm)
  have hf := flipIf_invol k (fun x : N n => x c = 1) (flip_local c k hck)
  have eq : Op k (fun x : N n => if x c = 1 then diagonal ![l, m] else 1) =
      diagonal (fun x => ![1, l] (x c)) * diagonal (fun x => ![1, β] (x c)) *
        diagonal (fun x => ![1, β] (x k)) *
        (Pm (flipIf k (fun x : N n => x c = 1)) * diagonal (fun x => ![1, star β] (x k)) *
          Pm (flipIf k (fun x : N n => x c = 1))) := by
    rw [Pm_conj_diag _ hf, diagonal_mul_diagonal, diagonal_mul_diagonal, diagonal_mul_diagonal]
    have : (fun x : N n => if x c = 1 then diagonal ![l, m] else (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun x => diagonal (if x c = 1 then ![l, m] else ![1, 1]) := by
      funext x; split_ifs
      · rfl
      · rw [← diagonal_one]; congr 1; funext i; fin_cases i <;> rfl
    rw [this, Op_diag]
    congr 1; funext x
    unfold flipIf
    by_cases hc : x c = 1
    · simp only [hc, if_true, Function.update_self]
      have hβu' := hβu
      simp only [Complex.star_def] at hβu'
      generalize x k = t; fin_cases t
      · simp; linear_combination (-l) * hβu'
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        have : (1 : Fin 2) + 1 = 0 := by decide
        rw [this]; simp only [Matrix.cons_val_zero, mul_one]
        rw [mul_assoc, hβ, ← mul_assoc, mul_comm l, hl, one_mul]
    · simp only [hc, if_false]
      have hc0 : x c = 0 := fin2_ne_one _ hc
      rw [hc0]
      generalize x k = t; fin_cases t
      · simp
      · simp only [Complex.star_def] at hβu
        simp; linear_combination (-1 : ℂ) * hβu
  rw [eq]
  refine ((InG.diag1 c l hl).mul (InG.diag1 c β hβu)).mul (InG.diag1 k β hβu) |>.mul
    (((InG.Pflip c k hck).mul (InG.diag1 k (star β) ?_)).mul (InG.Pflip c k hck))
  rw [star_star, mul_comm]; exact hβu

lemma InG.ctrl1 (c k : Fin n) (hck : c ≠ k) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ unitaryGroup (Fin 2) ℂ) :
    InG (Op k (fun x : N n => if x c = 1 then U else 1)) := by
  obtain ⟨W, hW, l, m, hl, hm, rfl⟩ := SCU2.diag2 U hU
  have hWW := mem_unitaryGroup_iff.mp hW
  have eq : Op k (fun x : N n => if x c = 1 then W * diagonal ![l, m] * star W else 1) =
      Op k (fun _ => W) * Op k (fun x : N n => if x c = 1 then diagonal ![l, m] else 1) *
        Op k (fun _ => star W) := by
    rw [Op_mul k _ _ (ctrl_local c k hck _ _), Op_mul k _ _ (fun _ _ => rfl)]
    congr 1; funext x; split_ifs
    · rfl
    · rw [mul_one, hWW]
  rw [eq]
  exact ((InG.onQubit' k W hW).mul (InG.ctrlDiag c k hck l m hl hm)).mul
    (InG.onQubit' k _ (Unitary.star_mem hW))

def Ctrl (S : Finset (Fin n)) (k : Fin n) (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (N n) (N n) ℂ :=
  Op k (fun x => if ∀ s ∈ S, x s = 1 then U else 1)

lemma pred_local (S : Finset (Fin n)) (k : Fin n) (hk : k ∉ S) (x : N n) (b : Fin 2) :
    (∀ s ∈ S, Function.update x k b s = 1) ↔ (∀ s ∈ S, x s = 1) := by
  constructor
  · intro h s hs; have := h s hs; rwa [Function.update_of_ne (by rintro rfl; exact hk hs)] at this
  · intro h s hs; rw [Function.update_of_ne (by rintro rfl; exact hk hs)]; exact h s hs

theorem InG.ctrl (S : Finset (Fin n)) : ∀ k, k ∉ S → ∀ U ∈ unitaryGroup (Fin 2) ℂ,
    InG (Ctrl S k U) := by
  induction S using Finset.induction_on with
  | empty =>
    intro k _ U hU
    have : Ctrl (∅ : Finset (Fin n)) k U = Op k (fun _ => U) := by
      unfold Ctrl; congr 1; funext x; simp
    rw [this]; exact InG.onQubit' k U hU
  | @insert c S' hc IH =>
    intro k hk U hU
    have hkc : c ≠ k := fun e => hk (e ▸ Finset.mem_insert_self _ _)
    have hkS : k ∉ S' := fun h => hk (Finset.mem_insert_of_mem h)
    obtain ⟨V, hV, hVV⟩ := SCU2.unitary_sqrt U hU
    have hV1 := mem_unitaryGroup_iff'.mp hV
    have hV2 := mem_unitaryGroup_iff.mp hV
    set p' : N n → Prop := fun x => ∀ s ∈ S', x s = 1 with hp'
    have hpc : ∀ (x : N n) b, p' (Function.update x c b) ↔ p' x := pred_local S' c hc
    have hpk : ∀ (x : N n) b, p' (Function.update x k b) ↔ p' x := pred_local S' k hkS
    have hφ := flipIf_invol c p' hpc
    have hφk : ∀ (x : N n) b, flipIf c p' (Function.update x k b) =
        Function.update (flipIf c p' x) k b := by
      intro x b
      unfold flipIf
      by_cases h : p' x
      · rw [if_pos ((hpk x b).mpr h), if_pos h, Function.update_of_ne hkc,
          Function.update_comm hkc.symm]
      · rw [if_neg (fun h' => h ((hpk x b).mp h')), if_neg h]
    have hφc : ∀ x : N n, flipIf c p' x c = if p' x then x c + 1 else x c := by
      intro x; unfold flipIf; split_ifs <;> simp
    have hXflip : Ctrl S' c Xm = Pm (flipIf c p') := Op_flip c p' hpc
    have eq : Ctrl (insert c S') k U =
        Op k (fun x : N n => if x c = 1 then V else 1) *
          (Pm (flipIf c p') * Op k (fun x : N n => if x c = 1 then star V else 1) *
            Pm (flipIf c p')) *
          Op k (fun x : N n => if p' x then V else 1) := by
      rw [Pm_conj_Op _ hφ k hφk]
      have hl2 : Local k (fun x : N n => if flipIf c p' x c = 1 then star V else 1) := by
        intro x b; simp only [hφk, Function.update_of_ne hkc]
      have hl3 : Local k (fun x : N n => if p' x then V else 1) := by
        intro x b; simp only [hpk]
      rw [Op_mul k _ _ hl2, Op_mul k _ _ hl3]
      unfold Ctrl
      congr 1; funext x
      rw [hφc]
      simp only [Finset.mem_insert, forall_eq_or_imp]
      by_cases hp : p' x
      · have hp2 : ∀ s ∈ S', x s = 1 := hp
        rw [if_pos hp, if_pos hp]
        by_cases hx : x c = 1
        · have : x c + 1 ≠ 1 := by rw [hx]; decide
          rw [if_pos ⟨hx, hp2⟩, if_pos hx, if_neg this, mul_one, hVV]
        · have : x c + 1 = 1 := by rw [fin2_ne_one _ hx]; decide
          rw [if_neg (fun h => hx h.1), if_neg hx, if_pos this, one_mul, hV1]
      · have hp2 : ¬ ∀ s ∈ S', x s = 1 := hp
        rw [if_neg hp, if_neg hp, mul_one, if_neg (fun h => hp2 h.2)]
        by_cases hx : x c = 1
        · rw [if_pos hx, if_pos hx, hV2]
        · rw [if_neg hx, if_neg hx, one_mul]
    rw [eq]
    have hP : InG (Pm (flipIf c p')) := by
      rw [← hXflip]; exact IH c hc Xm Xm_unitary
    exact ((InG.ctrl1 c k hkc V hV).mul ((hP.mul (InG.ctrl1 c k hkc _ (Unitary.star_mem hV))).mul hP)).mul
      (IH k hkS V hV)

end SCU


open scoped Matrix Kronecker

namespace SCU
open Matrix SuperconductingQC

set_option linter.unusedSectionVars false
variable {n : ℕ}

lemma Pm_mul (f g : N n → N n) : Pm f * Pm g = Pm (fun y => f (g y)) := by
  ext x y
  rw [mul_apply, Finset.sum_eq_single (g y)]
  · simp [Pm]
  · intro z _ hz; simp [Pm, hz]
  · simp

lemma Pm_id : Pm (fun y : N n => y) = 1 := by
  ext x y; simp [Pm, one_apply]

lemma InG.one : InG (1 : Matrix (N n) (N n) ℂ) := ⟨1, Subgroup.one_mem _, rfl⟩

lemma InG.flip (k : Fin n) : InG (Pm (fun y : N n => y + Pi.single k 1)) := by
  have h1 : Op k (fun _ => Xm) = Pm (flipIf k (fun _ : N n => True)) := by
    rw [← Op_flip k (fun _ : N n => True) (fun _ _ => Iff.rfl)]; simp
  have h2 : flipIf k (fun _ : N n => True) = fun y => y + Pi.single k 1 := by
    funext y j; unfold flipIf; rw [if_pos trivial]
    by_cases hj : j = k
    · subst hj; simp
    · simp [Function.update_of_ne hj, Pi.single_apply, hj]
  rw [← h2, ← h1]; exact InG.onQubit' k Xm Xm_unitary

lemma InG.trans (w : N n) : InG (Pm (fun y : N n => y + w)) := by
  have key : ∀ T : Finset (Fin n),
      InG (Pm (fun y : N n => y + (fun j => if j ∈ T then (1 : Fin 2) else 0))) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : (fun y : N n => y + (fun j => if j ∈ (∅ : Finset (Fin n)) then (1 : Fin 2) else 0)) =
          fun y => y := by funext y j; simp
      rw [this, Pm_id]; exact InG.one
    | @insert j T hj IH =>
      have h := (InG.flip j).mul IH
      rw [Pm_mul] at h
      convert h using 2
      funext y l
      simp only [Pi.add_apply, Finset.mem_insert, Pi.single_apply]
      by_cases hl : l = j
      · subst hl; simp [hj]
      · simp [hl]
  have hw : w = fun j => if j ∈ Finset.univ.filter (fun j => w j = 1) then (1 : Fin 2) else 0 := by
    funext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact h
    · exact fin2_ne_one _ h
  rw [hw]; exact key _

lemma trans_invol (w : N n) (y : N n) : y + w + w = y := by
  funext j; simp only [Pi.add_apply]; generalize y j = s; generalize w j = t
  fin_cases s <;> fin_cases t <;> decide

lemma add_eq_iff (x a w : N n) : x + w = a + w ↔ x = a := by
  constructor
  · intro h; have := congrArg (· + w) h; simpa [trans_invol] using this
  · rintro rfl; rfl

/-! phases -/
lemma InG.phase (hn : 0 < n) (a : N n) (z : ℂ) (hz : star z * z = 1) :
    InG (diagonal (Function.update (fun _ => (1 : ℂ)) a z)) := by
  set k : Fin n := ⟨0, hn⟩
  set ones : N n := fun _ => 1
  have hC : Ctrl (Finset.univ.erase k) k (diagonal ![1, z]) =
      diagonal (Function.update (fun _ => (1 : ℂ)) ones z) := by
    unfold Ctrl
    have : (fun x : N n => if ∀ s ∈ Finset.univ.erase k, x s = 1 then diagonal ![1, z] else
        (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun x => diagonal (if ∀ s ∈ Finset.univ.erase k, x s = 1 then ![1, z] else ![1, 1]) := by
      funext x; split_ifs
      · rfl
      · rw [← diagonal_one]; congr 1; funext i; fin_cases i <;> rfl
    rw [this, Op_diag]
    congr 1; funext x
    rw [Function.update_apply]
    by_cases hx : ∀ s ∈ Finset.univ.erase k, x s = 1
    · rw [if_pos hx]
      by_cases hk : x k = 1
      · have : x = ones := by
          funext s; by_cases hs : s = k
          · subst hs; exact hk
          · exact hx s (Finset.mem_erase.mpr ⟨hs, Finset.mem_univ _⟩)
        rw [if_pos this, hk]; rfl
      · have : x ≠ ones := fun e => hk (by rw [e])
        rw [if_neg this, fin2_ne_one _ hk]; rfl
    · rw [if_neg hx, if_neg]
      · generalize x k = t; fin_cases t <;> rfl
      · rintro rfl; exact hx fun _ _ => rfl
  have hw := trans_invol (a + ones)
  have hconj := Pm_conj_diag (fun y : N n => y + (a + ones)) (fun y => hw y)
    (Function.update (fun _ => (1 : ℂ)) ones z)
  have : (fun x : N n => Function.update (fun _ => (1 : ℂ)) ones z (x + (a + ones))) =
      Function.update (fun _ => (1 : ℂ)) a z := by
    funext x
    rw [Function.update_apply, Function.update_apply]
    congr 1
    apply propext
    have hao : a + (a + ones) = ones := by
      funext j; simp only [Pi.add_apply]; generalize a j = t; generalize ones j = u
      fin_cases t <;> fin_cases u <;> decide
    have := add_eq_iff x a (a + ones)
    rw [hao] at this
    exact this
  rw [this] at hconj
  rw [← hconj, ← hC]
  have hU : diagonal ![1, z] ∈ unitaryGroup (Fin 2) ℂ := diag_unit z hz
  exact ((InG.trans _).mul (InG.ctrl _ k (by simp) _ hU)).mul (InG.trans _)

open SCTwo in
lemma embedM_apply (a b : N n) (hab : a ≠ b) (M : Matrix (Fin 2) (Fin 2) ℂ) (x y : N n) :
    embedM a b hab M x y =
      if x = a then M 0 0 * (1 : Matrix (N n) (N n) ℂ) a y + M 0 1 * (1 : Matrix (N n) (N n) ℂ) b y
      else if x = b then M 1 0 * (1 : Matrix (N n) (N n) ℂ) a y + M 1 1 * (1 : Matrix (N n) (N n) ℂ) b y
      else (1 : Matrix (N n) (N n) ℂ) x y := by
  rw [← embedM_mul_apply a b hab M 1 x y, Matrix.mul_one]

open SCTwo in
lemma Pm_conj_embedM (φ : N n → N n) (hφ : ∀ y, φ (φ y) = y) (a b : N n) (hab : a ≠ b)
    (hab' : φ a ≠ φ b) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Pm φ * embedM a b hab M * Pm φ = embedM (φ a) (φ b) hab' M := by
  have e1 : ∀ u v, (φ u = v) ↔ (u = φ v) :=
    fun u v => ⟨fun h => by rw [← h, hφ], fun h => by rw [h, hφ]⟩
  have e2 : ∀ u v, (1 : Matrix (N n) (N n) ℂ) u (φ v) = (1 : Matrix (N n) (N n) ℂ) (φ u) v := by
    intro u v; simp only [one_apply]
    congr 1; apply propext; constructor
    · intro h; rw [h, hφ]
    · intro h; rw [← h, hφ]
  ext x y
  rw [Pm_conj_apply φ hφ, embedM_apply, embedM_apply, e2, e2, e2]
  simp only [e1]
  rw [hφ x]

lemma InG.toUnitary {A : Matrix (N n) (N n) ℂ} (hA : InG A) (h : A ∈ unitaryGroup (N n) ℂ) :
    (⟨A, h⟩ : unitaryGroup (N n) ℂ) ∈ GG n := by
  obtain ⟨W, hW, hWA⟩ := hA
  have : W = ⟨A, h⟩ := Subtype.ext hWA
  rwa [← this]

open SCTwo in
lemma embedM_ctrl (k : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (h : Function.update (fun _ => (1 : Fin 2)) k 0 ≠ fun _ => 1) :
    embedM (Function.update (fun _ => (1 : Fin 2)) k 0) (fun _ => 1) h M =
      Ctrl (Finset.univ.erase k) k M := by
  ext x y
  rw [embedM_apply]
  unfold Ctrl Op
  beta_reduce
  set ones : N n := fun _ => 1 with hones
  set o0 : N n := Function.update ones k 0 with ho0
  set P : N n → Prop := fun x => ∀ s ∈ Finset.univ.erase k, x s = 1 with hP
  have hPx : ∀ x : N n, P x ↔ ∀ s, s ≠ k → x s = 1 := by
    intro x; simp only [hP, Finset.mem_erase, Finset.mem_univ, and_true]
  have hxo : ∀ x : N n, x = o0 ↔ P x ∧ x k = 0 := by
    intro x; rw [hPx]; constructor
    · rintro rfl; refine ⟨fun s hs => ?_, by simp [ho0]⟩
      simp [ho0, Function.update_of_ne hs, hones]
    · rintro ⟨h1, h2⟩; funext s; by_cases hs : s = k
      · subst hs; simp [ho0, h2]
      · simp [ho0, Function.update_of_ne hs, h1 s hs, hones]
  have hxl : ∀ x : N n, x = ones ↔ P x ∧ x k = 1 := by
    intro x; rw [hPx]; constructor
    · rintro rfl; exact ⟨fun _ _ => rfl, rfl⟩
    · rintro ⟨h1, h2⟩; funext s; by_cases hs : s = k
      · subst hs; exact h2
      · exact h1 s hs
  have hagree : ∀ s, s ≠ k → o0 s = ones s := fun s hs => by simp [ho0, Function.update_of_ne hs]
  by_cases hxy : ∀ j, j ≠ k → x j = y j
  · rw [if_pos hxy]
    have hPy : P y ↔ P x := by
      rw [hPx, hPx]; constructor
      · intro h s hs; rw [hxy s hs]; exact h s hs
      · intro h s hs; rw [← hxy s hs]; exact h s hs
    by_cases hPx' : P x
    · have hPy' := hPy.mpr hPx'
      rw [if_pos hPx']
      have hx2 : x k = 0 ∨ x k = 1 := by generalize x k = t; fin_cases t <;> simp
      have hy2 : y k = 0 ∨ y k = 1 := by generalize y k = t; fin_cases t <;> simp
      have hne : o0 ≠ ones := h
      have ho0k : o0 k = 0 := by simp [ho0]
      have hlk : ones k = 1 := rfl
      rcases hx2 with hx | hx <;> rcases hy2 with hy | hy
      · obtain rfl := (hxo x).mpr ⟨hPx', hx⟩; obtain rfl := (hxo y).mpr ⟨hPy', hy⟩
        simp [one_apply, hne, hne.symm, ho0k]
      · obtain rfl := (hxo x).mpr ⟨hPx', hx⟩; obtain rfl := (hxl y).mpr ⟨hPy', hy⟩
        simp [one_apply, hne, hne.symm, ho0k, hlk]
      · obtain rfl := (hxl x).mpr ⟨hPx', hx⟩; obtain rfl := (hxo y).mpr ⟨hPy', hy⟩
        simp [one_apply, hne, hne.symm, ho0k, hlk]
      · obtain rfl := (hxl x).mpr ⟨hPx', hx⟩; obtain rfl := (hxl y).mpr ⟨hPy', hy⟩
        simp [one_apply, hne, hne.symm, hlk]
    · rw [if_neg hPx', if_neg (fun e => hPx' ((hxo x).mp e).1),
        if_neg (fun e => hPx' ((hxl x).mp e).1), one_apply, one_apply]
      congr 1; apply propext; constructor
      · rintro rfl; rfl
      · intro e; funext j; by_cases hj : j = k
        · subst hj; exact e
        · exact hxy j hj
  · rw [if_neg hxy]
    have hy0 : x = o0 → y ≠ o0 ∧ y ≠ ones := by
      rintro rfl; constructor
      · rintro rfl; exact hxy fun _ _ => rfl
      · rintro rfl; exact hxy hagree
    have hy1 : x = ones → y ≠ o0 ∧ y ≠ ones := by
      rintro rfl; constructor
      · rintro rfl; exact hxy fun s hs => (hagree s hs).symm
      · rintro rfl; exact hxy fun _ _ => rfl
    split_ifs with h1 h2
    · obtain ⟨n1, n2⟩ := hy0 h1
      rw [one_apply_ne (Ne.symm n1), one_apply_ne (Ne.symm n2)]; ring
    · obtain ⟨n1, n2⟩ := hy1 h2
      rw [one_apply_ne (Ne.symm n1), one_apply_ne (Ne.symm n2)]; ring
    · rw [one_apply_ne]; rintro rfl; exact hxy fun _ _ => rfl

open SCTwo in
lemma embedM_congr {a b a' b' : N n} (h1 : a = a') (h2 : b = b') (hab : a ≠ b) (hab' : a' ≠ b')
    (M : Matrix (Fin 2) (Fin 2) ℂ) : embedM a b hab M = embedM a' b' hab' M := by
  subst h1; subst h2; rfl

lemma fin2_succ : ∀ s t : Fin 2, s ≠ t → t = s + 1 := by decide

open SCTwo in
lemma InG.embed_base (k : Fin n) (a : N n) (ha : a k = 0) (hab : a ≠ Function.update a k 1)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ unitaryGroup (Fin 2) ℂ) :
    InG (embedM a (Function.update a k 1) hab M) := by
  set ones : N n := fun _ => 1
  set o0 : N n := Function.update ones k 0
  have hne : o0 ≠ ones := by
    intro e; have := congrFun e k; simp [o0, ones] at this
  set w : N n := a + o0
  have hw := trans_invol w
  have e1 : o0 + w = a := by
    funext j; simp only [w, Pi.add_apply]; generalize a j = t; generalize o0 j = u
    fin_cases t <;> fin_cases u <;> decide
  have e2 : ones + w = Function.update a k 1 := by
    funext j; simp only [w, o0, Pi.add_apply]
    by_cases hj : j = k
    · subst hj; simp [ha, ones]
    · simp only [Function.update_of_ne hj, ones]; generalize a j = t; fin_cases t <;> decide
  have hconj := Pm_conj_embedM (fun y : N n => y + w) (fun y => hw y) o0 ones hne
    (by simp only [e1, e2]; exact hab) M
  rw [embedM_congr e1 e2 _ hab] at hconj
  rw [← hconj, embedM_ctrl k M hne]
  exact ((InG.trans w).mul (InG.ctrl _ k (by simp) M hM)).mul (InG.trans w)

open SCTwo in
lemma InG.embed_move (k : Fin n) (a : N n) (ha : a k = 0) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M ∈ unitaryGroup (Fin 2) ℂ) (D : Finset (Fin n)) :
    ∀ b (hab : a ≠ b), b k = 1 → (∀ j, (j ≠ k ∧ a j ≠ b j) ↔ j ∈ D) →
      InG (embedM a b hab M) := by
  induction D using Finset.induction_on with
  | empty =>
    intro b hab hb hD
    have e : b = Function.update a k 1 := by
      funext j; by_cases hj : j = k
      · subst hj; simp [hb]
      · rw [Function.update_of_ne hj]
        by_contra h
        exact Finset.notMem_empty j ((hD j).mp ⟨hj, Ne.symm h⟩)
    have hab' : a ≠ Function.update a k 1 := e ▸ hab
    rw [embedM_congr rfl e hab hab']
    exact InG.embed_base k a ha hab' M hM
  | @insert j D hjD IH =>
    intro b hab hb hD
    obtain ⟨hjk, hjab⟩ := (hD j).mpr (Finset.mem_insert_self _ _)
    set b' := Function.update b j (a j)
    have hb' : b' k = 1 := by simp [b', Function.update_of_ne (Ne.symm hjk), hb]
    have hab' : a ≠ b' := fun e => by have := congrFun e k; rw [ha, hb'] at this; exact absurd this (by decide)
    have hD' : ∀ l, (l ≠ k ∧ a l ≠ b' l) ↔ l ∈ D := by
      intro l
      by_cases hl : l = j
      · subst hl; simp [b', hjD]
      · rw [show b' l = b l from Function.update_of_ne hl _ _, hD l, Finset.mem_insert]
        simp [hl]
    have hIH := IH b' hab' hb' hD'
    set φ := flipIf j (fun x : N n => x k = 1)
    have hφ := flipIf_invol j (fun x : N n => x k = 1) (flip_local k j (Ne.symm hjk))
    have hφa : φ a = a := by
      simp only [φ, flipIf]; rw [if_neg]; rw [ha]; decide
    have hφb : φ b' = b := by
      simp only [φ, flipIf]; rw [if_pos hb']
      funext l; by_cases hl : l = j
      · subst hl; simp [b', fin2_succ _ _ hjab]
      · simp [b', Function.update_of_ne hl]
    have hconj := Pm_conj_embedM φ hφ a b' hab' (by rw [hφa, hφb]; exact hab) M
    rw [embedM_congr hφa hφb _ hab] at hconj
    rw [← hconj]
    exact ((InG.Pflip k j (Ne.symm hjk)).mul hIH).mul (InG.Pflip k j (Ne.symm hjk))

open SCTwo in
lemma InG.embed (a b : N n) (hab : a ≠ b) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M ∈ unitaryGroup (Fin 2) ℂ) : InG (embedM a b hab M) := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hab
  have hgen : ∀ a b (hab : a ≠ b), a k = 0 → b k = 1 → InG (embedM a b hab M) := by
    intro a b hab ha hb
    exact InG.embed_move k a ha M hM (Finset.univ.filter fun j => j ≠ k ∧ a j ≠ b j) b hab hb
      (fun j => by simp)
  have h2 : a k = 0 ∨ a k = 1 := by generalize a k = t; fin_cases t <;> simp
  rcases h2 with ha | ha
  · exact hgen a b hab ha (by rw [fin2_succ _ _ hk, ha]; decide)
  · have hb : b k = 0 := by rw [fin2_succ _ _ hk, ha]; decide
    set ψ : N n → N n := fun y => y + Pi.single k 1
    have hψ : ∀ y, ψ (ψ y) = y := fun y => trans_invol _ y
    have hne : ψ a ≠ ψ b := fun e => hab (by rw [← hψ a, e, hψ])
    have hconj := Pm_conj_embedM ψ hψ (ψ a) (ψ b) hne (by rw [hψ, hψ]; exact hab) M
    rw [embedM_congr (hψ a) (hψ b) _ hab] at hconj
    rw [← hconj]
    refine ((InG.flip k).mul (hgen _ _ hne ?_ ?_)).mul (InG.flip k)
    · simp [ψ, ha]
    · simp [ψ, hb]

theorem cnot_univ (n : ℕ) (hn : 1 ≤ n) : GG n = ⊤ :=
  SCTwo.mainK (GG n) (fun a z h hz => (InG.phase hn a z hz).toUnitary h)
    (fun a b hab M hM => (InG.embed a b hab M hM).toUnitary _)

end SCU


open SuperconductingQC in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    Subgroup.closure (singleQubitGates n ∪ twoQubitGateInstances n CNOT) = ⊤ :=
  SCU.cnot_univ n hn
