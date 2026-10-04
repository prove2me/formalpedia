-- Prove2me | solution 2 for VanderbeiLP.Simplex.lexicographic_rule_terminates
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T21:31:47.956325+00:00
-- url     : https://prove2.me/submissions/0fcc1ac6-8f0f-49ef-a207-d182b812cfc7

import Mathlib
import Definitions.Def_VanderbeiLP_Simplex_Dictionary
import Definitions.Def_VanderbeiLP_Simplex_PivotRules
import Definitions.Def_VanderbeiLP_Simplex_StandardForm

set_option autoImplicit false

-- The finite-dictionary injectivity argument follows the accepted cycling proof
-- by Nickrobbins95, submission 3388be52-0240-4a10-826f-b7ea7eecf927.


namespace VanderbeiLP.Simplex
open Module Finset
noncomputable section
variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}

lemma bl_basis (D : Dictionary A) (i : D.B) : D.colBasis i = augCol A i := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i

lemma bl_bbar_not (D : Dictionary A) (v : Fin m → ℝ) {i : Fin (n+m)}
    (hi : i ∉ D.B) : D.bbar v i = 0 := by simp [Dictionary.bbar,hi]

lemma bl_bbar_mem (D : Dictionary A) (v : Fin m → ℝ) (i : D.B) :
    D.bbar v i = D.colBasis.repr v i := by simp [Dictionary.bbar,i.property]

lemma bl_bbar_add (D : Dictionary A) (u v : Fin m → ℝ) (i : Fin (n+m)) :
    D.bbar (u+v) i = D.bbar u i + D.bbar v i := by
  classical
  by_cases hi : i ∈ D.B <;> simp [Dictionary.bbar,hi]

lemma bl_bbar_smul (D : Dictionary A) (r : ℝ) (v : Fin m → ℝ) (i : Fin (n+m)) :
    D.bbar (r • v) i = r * D.bbar v i := by
  classical
  by_cases hi : i ∈ D.B <;> simp [Dictionary.bbar,hi]

lemma bl_bbar_zero (D : Dictionary A) (i : Fin (n+m)) : D.bbar 0 i = 0 := by
  classical
  simp [Dictionary.bbar]

lemma bl_bbar_sum {ι : Type*} (D : Dictionary A) (s : Finset ι)
    (v : ι → Fin m → ℝ) (i : Fin (n+m)) :
    D.bbar (∑ j ∈ s, v j) i = ∑ j ∈ s, D.bbar (v j) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bl_bbar_zero]
  | @insert j s hj ih => simp [hj,bl_bbar_add,ih]

lemma bl_abar_col (D : Dictionary A) (i j : Fin (n+m)) :
    D.bbar (augCol A j) i = D.abar i j := rfl

lemma bl_abar_basic (D : Dictionary A) {j : Fin (n+m)} (hj : j ∈ D.B)
    (i : Fin (n+m)) : D.abar i j = if i=j then 1 else 0 := by
  classical
  by_cases hi : i ∈ D.B
  · have h := D.colBasis.repr_self ⟨j,hj⟩
    have h' := congrArg (fun f => f ⟨i,hi⟩) h
    rw [bl_basis] at h'
    simpa [Dictionary.abar,hi,Finsupp.single_apply,Subtype.ext_iff,eq_comm] using h'
  · have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp [Dictionary.abar,hi,hij]

lemma bl_repr (D : Dictionary A) (v : Fin m → ℝ) :
    ∑ i ∈ D.B, D.bbar v i • augCol A i = v := by
  classical
  have h := D.colBasis.sum_repr v
  simp_rw [bl_basis,← bl_bbar_mem] at h
  calc
    _ = ∑ i : D.B, D.bbar v i • augCol A i :=
      (Finset.sum_coe_sort D.B (fun i => D.bbar v i • augCol A i)).symm
    _ = v := h

lemma bl_repr_all (D : Dictionary A) (v : Fin m → ℝ) :
    ∑ i, D.bbar v i • augCol A i = v := by
  classical
  calc
    _ = ∑ i ∈ D.B, D.bbar v i • augCol A i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp [bl_bbar_not D v hi]
    _ = v := bl_repr D v

lemma bl_coord_eq (D : Dictionary A) (z : Fin (n+m) → ℝ) (v : Fin m → ℝ)
    (hz : ∑ j, z j • augCol A j = v) (i : Fin (n+m)) :
    D.bbar v i = ∑ j, z j * D.abar i j := by
  rw [← hz,bl_bbar_sum]
  simp_rw [bl_bbar_smul,bl_abar_col]

lemma bl_unique (D : Dictionary A) (z : Fin (n+m) → ℝ) (v : Fin m → ℝ)
    (hz : ∑ j, z j • augCol A j = v) (hs : ∀ j ∉ D.B, z j=0) : z=D.bbar v := by
  classical
  ext i
  by_cases hi : i ∈ D.B
  · rw [bl_coord_eq D z v hz i]
    symm
    rw [← Finset.sum_subset (Finset.subset_univ D.B) (fun j _ hj => by simp [hs j hj])]
    calc
      _ = ∑ j ∈ D.B, z j * (if i=j then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [bl_abar_basic D hj]
      _ = z i := by simp [hi,eq_comm]
  · simp [hs i hi,bl_bbar_not D v hi]

lemma bl_cbar_basic (D : Dictionary A) (c : Fin n → ℝ)
    {j : Fin (n+m)} (hj : j ∈ D.B) : D.cbar c j=0 := by
  classical
  simp [Dictionary.cbar,bl_abar_basic D hj,hj]

lemma bl_cost_eq (D : Dictionary A) (c z : Fin (n+m) → ℝ) (v : Fin m → ℝ)
    (hz : ∑ j, z j • augCol A j=v) :
    ∑ j, c j*z j = (∑ i ∈ D.B, c i*D.bbar v i) +
      ∑ j, (c j-∑ i ∈ D.B, c i*D.abar i j)*z j := by
  classical
  have h : (∑ i ∈ D.B, c i*D.bbar v i) =
      ∑ j, (∑ i ∈ D.B, c i*D.abar i j)*z j := by
    simp_rw [bl_coord_eq D z v hz,mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h]
  simp_rw [sub_mul,Finset.sum_sub_distrib]
  ring

end
end VanderbeiLP.Simplex


namespace VanderbeiLP.Simplex
open Module Finset
noncomputable section
variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}

def bl_coord (D : Dictionary A) (i : Fin (n+m)) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun v := D.bbar v i
  map_add' u v := bl_bbar_add D u v i
  map_smul' r v := bl_bbar_smul D r v i

lemma bl_exchange (D : Dictionary A) {k l : Fin (n+m)} (hk : k ∉ D.B)
    (hl : l ∈ D.B) (ha : D.abar l k ≠ 0) :
    ∃ D' : Dictionary A, D'.B=insert k (D.B.erase l) := by
  classical
  have hli : LinearIndepOn ℝ (augCol A) (↑D.B : Set (Fin (n+m))) := D.linearIndependent
  have he : LinearIndepOn ℝ (augCol A) (↑(D.B.erase l) : Set (Fin (n+m))) :=
    hli.mono (by intro i hi; exact (Finset.mem_erase.mp hi).2)
  have hnot : augCol A k ∉ Submodule.span ℝ (augCol A '' (↑(D.B.erase l) : Set (Fin (n+m)))) := by
    intro h
    have hker : Submodule.span ℝ (augCol A '' (↑(D.B.erase l) : Set (Fin (n+m)))) ≤
        LinearMap.ker (bl_coord D l) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,hj,rfl⟩
      change D.abar l j=0
      rw [bl_abar_basic D (Finset.mem_erase.mp hj).2]
      simp [(Finset.mem_erase.mp hj).1.symm]
    have hzero := hker h
    exact ha hzero
  have hnew : LinearIndepOn ℝ (augCol A) (↑(insert k (D.B.erase l)) : Set (Fin (n+m))) := by
    simpa only [Finset.coe_insert] using he.insert hnot
  refine ⟨⟨insert k (D.B.erase l),?_,hnew⟩,rfl⟩
  rw [Finset.card_insert_of_notMem (fun h => hk (Finset.mem_erase.mp h).2),
    Finset.card_erase_of_mem hl]
  have hc := D.card_B
  have hp := Finset.card_pos.mpr ⟨l,hl⟩
  omega

def bl_dir (D : Dictionary A) (k : Fin (n+m)) : Fin (n+m) → ℝ :=
  Pi.single k 1 - fun i => D.abar i k

lemma bl_abar_not (D : Dictionary A) {i : Fin (n+m)} (hi : i ∉ D.B)
    (j : Fin (n+m)) : D.abar i j=0 := by simp [Dictionary.abar,hi]

lemma bl_dir_self (D : Dictionary A) {k : Fin (n+m)} (hk : k ∉ D.B) :
    bl_dir D k k=1 := by simp [bl_dir,bl_abar_not D hk]

lemma bl_dir_other (D : Dictionary A) {k i : Fin (n+m)} (hi : i ≠ k) :
    bl_dir D k i= -D.abar i k := by simp [bl_dir,hi]

lemma bl_dir_col (D : Dictionary A) (k : Fin (n+m)) :
    ∑ i, bl_dir D k i • augCol A i=0 := by
  classical
  simp only [bl_dir,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]
  have hs : (∑ i, Pi.single (M := fun _ => ℝ) k (1:ℝ) i • augCol A i)=augCol A k := by
    simp [Pi.single_apply]
  rw [hs]
  have h := bl_repr_all D (augCol A k)
  simp_rw [bl_abar_col] at h
  rw [h,sub_self]

lemma bl_dir_cost (D : Dictionary A) (c : Fin n → ℝ) (k : Fin (n+m)) :
    ∑ i, extCost c i*bl_dir D k i=D.cbar c k := by
  classical
  simp only [bl_dir,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,Dictionary.cbar]
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  congr 1
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  simp [bl_abar_not D hi]

lemma bl_pivot_rhs (D D' : Dictionary A) {k l : Fin (n+m)} (hk : k ∉ D.B)
    (hl : l ∈ D.B) (ha : D.abar l k ≠ 0) (hB : D'.B=insert k (D.B.erase l))
    (v : Fin m → ℝ) :
    D'.bbar v=D.bbar v+(D.bbar v l/D.abar l k) • bl_dir D k := by
  classical
  let θ := D.bbar v l/D.abar l k
  apply Eq.symm
  apply bl_unique D'
  · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_smul,mul_smul,
      Finset.sum_add_distrib,← Finset.smul_sum,bl_repr_all,bl_dir_col,smul_zero,add_zero]
  · intro i hi
    have hik : i ≠ k := by intro h; subst i; exact hi (hB ▸ Finset.mem_insert_self _ _)
    rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul,bl_dir_other D hik]
    by_cases hil : i=l
    · subst i
      field_simp [ha]
      ring
    · have hin : i ∉ D.B := by
        intro h
        exact hi (hB ▸ Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hil,h⟩))
      simp [bl_bbar_not D v hin,bl_abar_not D hin]

lemma bl_zeta_pivot (D D' : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    {k l : Fin (n+m)} (hk : k ∉ D.B) (hl : l ∈ D.B) (ha : D.abar l k ≠ 0)
    (hB : D'.B=insert k (D.B.erase l)) :
    D'.zetaBar b c=D.zetaBar b c+(D.bbar b l/D.abar l k)*D.cbar c k := by
  classical
  have hsum (E : Dictionary A) : (∑ i, extCost c i*E.bbar b i)=E.zetaBar b c := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [bl_bbar_not E b hi]
  rw [← hsum D',bl_pivot_rhs D D' hk hl ha hB b]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
  rw [hsum D]
  have he : (∑ i, extCost c i*((D.bbar b l/D.abar l k)*bl_dir D k i)) =
      (D.bbar b l/D.abar l k)*(∑ i, extCost c i*bl_dir D k i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,bl_dir_cost]

end
end VanderbeiLP.Simplex


namespace VanderbeiLP.Simplex
open Finset
noncomputable section
variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}

lemma bl_lex_smul_lt {d : ℕ} {x y : Fin d → ℝ} {a : ℝ}
    (ha : 0 < a) (hxy : toLex x < toLex y) : toLex (a • x) < toLex (a • y) := by
  obtain ⟨i,hi,hlt⟩ := hxy
  refine ⟨i,?_,?_⟩
  · intro j hj
    change a*x j=a*y j
    simpa only [Pi.toLex_apply] using congrArg (fun z : ℝ => a*z) (hi j hj)
  · exact mul_lt_mul_of_pos_left hlt ha

lemma bl_lex_smul_le {d : ℕ} {x y : Fin d → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hxy : toLex x ≤ toLex y) : toLex (a • x) ≤ toLex (a • y) := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp
  rcases eq_or_lt_of_le hxy with he | hl
  · rw [toLex.injective he]
  · exact (bl_lex_smul_lt ha hl).le

lemma bl_eps_mem (D : Dictionary A) (p : Fin m) : D.epsVar p ∈ D.B :=
  Finset.orderEmbOfFin_mem _ _ _

lemma bl_eps_surj (D : Dictionary A) {i : Fin (n+m)} (hi : i ∈ D.B) :
    ∃ p : Fin m, D.epsVar p=i := by
  have h : i ∈ Set.range (D.B.orderEmbOfFin D.card_B) := by
    rw [Finset.range_orderEmbOfFin]
    exact hi
  exact h

lemma bl_lex_row_pivot (D₀ D D' : Dictionary A) (b : Fin m → ℝ)
    {k l : Fin (n+m)} (hk : k ∉ D.B) (hl : l ∈ D.B) (ha : D.abar l k ≠ 0)
    (hB : D'.B=insert k (D.B.erase l)) (i : Fin (n+m)) :
    Dictionary.lexRow D₀ D' b i = Dictionary.lexRow D₀ D b i +
      (bl_dir D k i/D.abar l k) • Dictionary.lexRow D₀ D b l := by
  ext j
  refine Fin.cases ?_ (fun p => ?_) j
  · have h := congrFun (bl_pivot_rhs D D' hk hl ha hB b) i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h
    simp only [Dictionary.lexRow,Fin.cons_zero,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [h]
    ring
  · have h := congrFun (bl_pivot_rhs D D' hk hl ha hB (augCol A (D₀.epsVar p))) i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,bl_abar_col] at h
    simp only [Dictionary.lexRow,Fin.cons_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [h]
    ring

lemma bl_lex_row_ne_zero (D₀ D : Dictionary A) (b : Fin m → ℝ)
    {i : Fin (n+m)} (hi : i ∈ D.B) : Dictionary.lexRow D₀ D b i ≠ 0 := by
  intro hzero
  have hz : ∀ j ∈ D₀.B, D.abar i j=0 := by
    intro j hj
    obtain ⟨p,rfl⟩ := bl_eps_surj D₀ hj
    have hh := congrFun hzero p.succ
    simpa only [Dictionary.lexRow,Fin.cons_succ,Pi.zero_apply] using hh
  have h := congrArg (fun v => D.bbar v i) (bl_repr D₀ (augCol A i))
  rw [bl_bbar_sum] at h
  simp_rw [bl_bbar_smul,bl_abar_col] at h
  have hsum : (∑ j ∈ D₀.B, D₀.abar j i*D.abar i j)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [hz j hj]
  rw [hsum,bl_abar_basic D hi] at h
  norm_num at h

lemma bl_lex_initial_pos (D₀ : Dictionary A) (b : Fin m → ℝ) (h0 : D₀.IsFeasible b)
    {i : Fin (n+m)} (hi : i ∈ D₀.B) : 0 < toLex (Dictionary.lexRow D₀ D₀ b i) := by
  classical
  by_cases hb : 0 < D₀.bbar b i
  · refine ⟨0,?_,?_⟩
    · intro j hj
      have hj0 : j.val < 0 := by simpa only [Fin.lt_def,Fin.val_zero] using hj
      omega
    · change 0 < D₀.bbar b i
      exact hb
  have hb0 : D₀.bbar b i=0 := le_antisymm (le_of_not_gt hb) (h0 i hi)
  obtain ⟨p,hp⟩ := bl_eps_surj D₀ hi
  refine ⟨p.succ,?_,?_⟩
  · intro j hj
    revert hj
    refine Fin.cases ?_ (fun q => ?_) j
    · intro _
      change 0 = D₀.bbar b i
      exact hb0.symm
    · intro hj
      have hq : q < p := by simpa only [Fin.succ_lt_succ_iff] using hj
      have hne : D₀.epsVar q ≠ i := by
        rw [← hp]
        exact (D₀.B.orderEmbOfFin D₀.card_B).injective.ne hq.ne
      change 0 = D₀.abar i (D₀.epsVar q)
      simp [bl_abar_basic D₀ (bl_eps_mem D₀ q),Ne.symm hne]
  · change 0 < D₀.abar i (D₀.epsVar p)
    rw [hp,bl_abar_basic D₀ hi]
    norm_num

end
end VanderbeiLP.Simplex


namespace VanderbeiLP.Simplex
open Finset
noncomputable section
variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}

lemma bl_lex_row_not (D₀ D : Dictionary A) (b : Fin m → ℝ)
    {i : Fin (n+m)} (hi : i ∉ D.B) : Dictionary.lexRow D₀ D b i=0 := by
  ext j
  refine Fin.cases ?_ (fun p => ?_) j
  · exact bl_bbar_not D b hi
  · exact bl_abar_not D hi _

lemma bl_lex_pivot_pos (D₀ D D' : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hpos : ∀ i ∈ D.B, 0 < toLex (Dictionary.lexRow D₀ D b i))
    (hp : Dictionary.IsLexPivot D₀ b c D D') :
    ∀ i ∈ D'.B, 0 < toLex (Dictionary.lexRow D₀ D' b i) := by
  classical
  rcases hp with ⟨k,l,⟨hk,hc⟩,⟨hl,ha,hmin⟩,hB⟩
  intro i hi
  have he := bl_lex_row_pivot D₀ D D' b hk hl ha.ne' hB i
  have hnn : 0 ≤ toLex (Dictionary.lexRow D₀ D' b i) := by
    rw [hB,Finset.mem_insert,Finset.mem_erase] at hi
    rcases hi with rfl | ⟨hil,hi⟩
    · rw [he,bl_lex_row_not D₀ D b hk,bl_dir_self D hk,zero_add]
      have hh := bl_lex_smul_lt (x := (0 : Fin (m+1) → ℝ)) (one_div_pos.mpr ha) (hpos l hl)
      simpa only [smul_zero,toLex_zero] using hh.le
    · have hik : i ≠ k := fun h => hk (h ▸ hi)
      rw [bl_dir_other D hik] at he
      by_cases hai : 0 < D.abar i k
      · have hm := bl_lex_smul_le hai.le (hmin i hi hai)
        have he' : Dictionary.lexRow D₀ D' b i = Dictionary.lexRow D₀ D b i -
            D.abar i k • ((D.abar l k)⁻¹ • Dictionary.lexRow D₀ D b l) := by
          rw [he]
          ext j
          simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
          simp only [div_eq_mul_inv]
          ring
        have hc' : D.abar i k • ((D.abar i k)⁻¹ • Dictionary.lexRow D₀ D b i)=
            Dictionary.lexRow D₀ D b i := by rw [smul_smul,mul_inv_cancel₀ hai.ne',one_smul]
        rw [hc'] at hm
        rw [he',toLex_sub]
        exact sub_nonneg.mpr hm
      · have hh := bl_lex_smul_le (x := (0 : Fin (m+1) → ℝ))
          (div_nonneg (neg_nonneg.mpr (le_of_not_gt hai)) ha.le)
          (hpos l hl).le
        simp only [smul_zero,toLex_zero] at hh
        rw [he,toLex_add]
        exact add_nonneg (hpos i hi).le hh
  have hne : toLex (Dictionary.lexRow D₀ D' b i) ≠ 0 := by
    intro hz
    exact bl_lex_row_ne_zero D₀ D' b hi (toLex.injective hz)
  exact lt_of_le_of_ne hnn hne.symm

def bl_lex_zeta (D₀ D : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Fin (m+1) → ℝ :=
  Fin.cons (D.zetaBar b c) (fun p => D.zetaBar (augCol A (D₀.epsVar p)) c)

lemma bl_lex_zeta_pivot (D₀ D D' : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    {k l : Fin (n+m)} (hk : k ∉ D.B) (hl : l ∈ D.B) (ha : D.abar l k ≠ 0)
    (hB : D'.B=insert k (D.B.erase l)) :
    bl_lex_zeta D₀ D' b c=bl_lex_zeta D₀ D b c +
      D.cbar c k • ((D.abar l k)⁻¹ • Dictionary.lexRow D₀ D b l) := by
  ext j
  refine Fin.cases ?_ (fun p => ?_) j
  · simp only [bl_lex_zeta,Dictionary.lexRow,Fin.cons_zero,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [bl_zeta_pivot D D' b c hk hl ha hB]
    ring
  · simp only [bl_lex_zeta,Dictionary.lexRow,Fin.cons_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [bl_zeta_pivot D D' (augCol A (D₀.epsVar p)) c hk hl ha hB,bl_abar_col]
    ring

lemma bl_lex_objective_strict (D₀ D D' : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hpos : ∀ i ∈ D.B, 0 < toLex (Dictionary.lexRow D₀ D b i))
    (hp : Dictionary.IsLexPivot D₀ b c D D') :
    toLex (bl_lex_zeta D₀ D b c) < toLex (bl_lex_zeta D₀ D' b c) := by
  rcases hp with ⟨k,l,⟨hk,hc⟩,⟨hl,ha,hmin⟩,hB⟩
  have h1 := bl_lex_smul_lt (x := (0 : Fin (m+1) → ℝ)) (inv_pos.mpr ha) (hpos l hl)
  simp only [smul_zero,toLex_zero] at h1
  have h2 := bl_lex_smul_lt (x := (0 : Fin (m+1) → ℝ)) hc h1
  simp only [smul_zero,toLex_zero] at h2
  rw [bl_lex_zeta_pivot D₀ D D' b c hk hl ha.ne' hB,toLex_add]
  exact lt_add_of_pos_right _ h2

lemma bl_lex_terminates (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (D₀ : Dictionary A) (h0 : D₀.IsFeasible b) :
    ¬ ∃ D : ℕ → Dictionary A, D 0=D₀ ∧ ∀ t, Dictionary.IsLexPivot D₀ b c (D t) (D (t+1)) := by
  classical
  rintro ⟨D,hD,hp⟩
  have hpos : ∀ t i, i ∈ (D t).B → 0 < toLex (Dictionary.lexRow D₀ (D t) b i) := by
    intro t
    induction t with
    | zero =>
      intro i hi
      exact (by simpa [hD] using bl_lex_initial_pos D₀ b h0 (by simpa [hD] using hi))
    | succ t ih => exact bl_lex_pivot_pos D₀ _ _ b c ih (hp t)
  have hstrict : StrictMono (fun t => toLex (bl_lex_zeta D₀ (D t) b c)) :=
    strictMono_nat_of_lt_succ (fun t => bl_lex_objective_strict D₀ _ _ b c (hpos t) (hp t))
  have hinj : Function.Injective (fun E : Dictionary A => E.B) := by
    rintro ⟨B1,h1,l1⟩ ⟨B2,h2,l2⟩ h
    simp only at h
    subst h
    rfl
  have : Finite (Dictionary A) := Finite.of_injective _ hinj
  obtain ⟨s,t,hne,heq⟩ := Finite.exists_ne_map_eq_of_infinite D
  apply hne
  exact hstrict.injective (congrArg (fun E => toLex (bl_lex_zeta D₀ E b c)) heq)

end
end VanderbeiLP.Simplex

open VanderbeiLP.Simplex

/-- **Vanderbei, Theorem 3.2 (p. 30).** The simplex method always terminates provided that the
leaving variable is selected by the lexicographic rule: started at any feasible dictionary
`D₀`, there is no infinite sequence of pivots in which each entering variable is an entering
candidate and each leaving variable is chosen by the lexicographic rule of the run started
at `D₀`. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (D₀ : Dictionary A) (h0 : D₀.IsFeasible b) :
    ¬ ∃ D : ℕ → Dictionary A, D 0 = D₀ ∧
      ∀ t, Dictionary.IsLexPivot D₀ b c (D t) (D (t + 1)) := by
  exact bl_lex_terminates A b c D₀ h0

#print axioms solution
