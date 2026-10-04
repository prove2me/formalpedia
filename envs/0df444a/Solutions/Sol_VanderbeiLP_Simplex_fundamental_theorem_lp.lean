-- Prove2me | solution 1 for VanderbeiLP.Simplex.fundamental_theorem_lp
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T21:34:25.953498+00:00
-- url     : https://prove2.me/submissions/4b0f5517-e9bb-4b5b-b370-516d009a93d6

import Mathlib
import Definitions.Def_VanderbeiLP_Simplex_Dictionary
import Definitions.Def_VanderbeiLP_Simplex_StandardForm
import Definitions.Def_VanderbeiLP_Simplex_StandardForm
import Theorems.Thm_VanderbeiLP_Simplex_nonterminating_implies_cycling

set_option autoImplicit false

-- The public cycling lemma is an accepted proof by Nickrobbins95, submission
-- 3388be52-0240-4a10-826f-b7ea7eecf927. All remaining proofs below are new.


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

lemma bl_pivot_feasible (D D' : Dictionary A) (b : Fin m → ℝ)
    {k l : Fin (n+m)} (h0 : D.IsFeasible b) (hk : k ∉ D.B)
    (hl : D.IsLeavingCandidate b k l) (hB : D'.B=insert k (D.B.erase l)) :
    D'.IsFeasible b := by
  classical
  rcases hl with ⟨hl,ha,hmin⟩
  have hθ : 0 ≤ D.bbar b l/D.abar l k := div_nonneg (h0 l hl) ha.le
  intro i hi
  have he := congrFun (bl_pivot_rhs D D' hk hl ha.ne' hB b) i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at he
  rw [hB,Finset.mem_insert,Finset.mem_erase] at hi
  rcases hi with rfl | ⟨hil,hi⟩
  · rw [he]
    simpa [bl_bbar_not D b hk,bl_dir_self D hk] using hθ
  · have hik : i ≠ k := fun h => hk (h ▸ hi)
    rw [bl_dir_other D hik] at he
    rw [he]
    by_cases hai : 0 < D.abar i k
    · have hh := (le_div_iff₀ hai).mp (hmin i hi hai)
      nlinarith
    · have hh : (D.bbar b l/D.abar l k)*D.abar i k ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hθ (le_of_not_gt hai)
      linarith [h0 i hi]

lemma bl_pivot_monotone (D D' : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (h0 : D.IsFeasible b) (hp : D.IsSimplexPivot b c D') :
    D.zetaBar b c ≤ D'.zetaBar b c := by
  rcases hp with ⟨k,l,⟨hk,hc⟩,⟨hl,ha,hmin⟩,hB⟩
  rw [bl_zeta_pivot D D' b c hk hl ha.ne' hB]
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (h0 l hl) ha.le) hc.le)

lemma bl_simplex_feasible (D D' : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (h0 : D.IsFeasible b) (hp : D.IsSimplexPivot b c D') : D'.IsFeasible b := by
  rcases hp with ⟨k,l,hk,hl,hB⟩
  exact bl_pivot_feasible D D' b h0 hk.1 hl hB

lemma bl_pivot_same (D D' : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hp : D.IsSimplexPivot b c D') (he : D'.zetaBar b c=D.zetaBar b c) :
    D'.bbar b=D.bbar b := by
  rcases hp with ⟨k,l,⟨hk,hc⟩,⟨hl,ha,hmin⟩,hB⟩
  have hz := bl_zeta_pivot D D' b c hk hl ha.ne' hB
  have hθ : D.bbar b l/D.abar l k=0 := by
    have hm : (D.bbar b l/D.abar l k)*D.cbar c k=0 := by linarith
    exact (mul_eq_zero.mp hm).resolve_right hc.ne'
  rw [bl_pivot_rhs D D' hk hl ha.ne' hB b,hθ,zero_smul,add_zero]

lemma bl_bland_simplex (D D' : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hp : D.IsBlandPivot b c D') : D.IsSimplexPivot b c D' := by
  rcases hp with ⟨k,l,hk,hl,hB⟩
  exact ⟨k,l,hk.1,hl.1,hB⟩

lemma bl_next (D : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hnt : ¬ D.IsBlandTerminal c) : ∃ D', D.IsBlandPivot b c D' := by
  classical
  have hex : ∃ k, D.IsEnteringCandidate c k := by
    by_contra hn
    apply hnt
    exact Or.inl (by simpa only [not_exists] using hn)
  let E := Finset.univ.filter (D.IsEnteringCandidate c)
  have hE : E.Nonempty := by simpa [E,Finset.Nonempty] using hex
  obtain ⟨k,hk,hkmin⟩ := Finset.exists_min_image E id hE
  have hk' : D.IsBlandEntering c k :=
    ⟨(Finset.mem_filter.mp hk).2, fun j hj => hkmin j (by simp [E,hj])⟩
  have hexl : ∃ l ∈ D.B, 0 < D.abar l k := by
    by_contra hn
    apply hnt
    refine Or.inr ⟨k,hk',?_⟩
    simpa only [not_exists,not_and,not_lt] using hn
  let L := D.B.filter (fun i => 0 < D.abar i k)
  have hL : L.Nonempty := by simpa [L,Finset.Nonempty] using hexl
  obtain ⟨l,hl,hlmin⟩ := Finset.exists_min_image L (fun i => D.bbar b i/D.abar i k) hL
  have hl' : D.IsLeavingCandidate b k l :=
    ⟨(Finset.mem_filter.mp hl).1,(Finset.mem_filter.mp hl).2,
      fun i hi ha => hlmin i (by simp [L,hi,ha])⟩
  let C := Finset.univ.filter (D.IsLeavingCandidate b k)
  have hC : C.Nonempty := ⟨l,by simp [C,hl']⟩
  obtain ⟨l',hl'',hl'min⟩ := Finset.exists_min_image C id hC
  have hl''' : D.IsBlandLeaving b k l' :=
    ⟨(Finset.mem_filter.mp hl'').2,fun i hi => hl'min i (by simp [C,hi])⟩
  obtain ⟨D',hB⟩ := bl_exchange D hk'.1.1 hl'''.1.1 hl'''.1.2.1.ne'
  exact ⟨D',k,l',hk',hl''',hB⟩

end
end VanderbeiLP.Simplex


namespace VanderbeiLP.Simplex
open Finset
noncomputable section
variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}

lemma bl_propagate (P : ℕ → Prop) (T : ℕ)
    (hstep : ∀ q < T, P q → P (q+1)) {r s : ℕ} (hrs : r ≤ s) (hs : s ≤ T)
    (hr : P r) : P s := by
  induction s,hrs using Nat.le_induction with
  | base => exact hr
  | succ s hrs ih => exact hstep s (by omega) (ih (by omega))

lemma bl_cycle_leave (P : ℕ → Prop) (T : ℕ) (hc : P 0 ↔ P T)
    (hy : ∃ r ≤ T, P r) (hn : ∃ s ≤ T, ¬ P s) :
    ∃ q < T, P q ∧ ¬ P (q+1) := by
  classical
  by_contra h
  have hstep : ∀ q < T, P q → P (q+1) := by
    intro q hq hp
    by_contra hnq
    exact h ⟨q,hq,hp,hnq⟩
  obtain ⟨r,hr,hpr⟩ := hy
  obtain ⟨s,hs,hns⟩ := hn
  have hPT := bl_propagate P T hstep hr le_rfl hpr
  exact hns (bl_propagate P T hstep (Nat.zero_le _) hs (hc.mpr hPT))

lemma bl_cycle_enter (P : ℕ → Prop) (T : ℕ) (hc : P 0 ↔ P T)
    (hy : ∃ r ≤ T, P r) (hn : ∃ s ≤ T, ¬ P s) :
    ∃ q < T, ¬ P q ∧ P (q+1) := by
  obtain ⟨q,hq,hnq,hp⟩ := bl_cycle_leave (fun q => ¬ P q) T (not_congr hc) hn
    (by simpa only [not_not] using hy)
  exact ⟨q,hq,hnq,not_not.mp hp⟩

lemma bl_no_bland_cycle (D : ℕ → Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (T : ℕ) (hT : 0 < T) (hcycle : D T=D 0) (h0 : (D 0).IsFeasible b)
    (hp : ∀ q < T, (D q).IsBlandPivot b c (D (q+1))) : False := by
  classical
  have hfeas : ∀ q ≤ T, (D q).IsFeasible b := by
    intro q hq
    induction q with
    | zero => exact h0
    | succ q ih =>
      exact bl_simplex_feasible _ _ b c (ih (by omega))
        (bl_bland_simplex _ _ b c (hp q (by omega)))
  have hmono : MonotoneOn (fun q => (D q).zetaBar b c) (Set.Iic T) := by
    intro r hr s hs hrs
    change r ≤ T at hr
    change s ≤ T at hs
    induction s,hrs using Nat.le_induction with
    | base => exact le_rfl
    | succ s hrs ih =>
      exact (ih (by omega)).trans (bl_pivot_monotone _ _ b c
        (hfeas s (by omega)) (bl_bland_simplex _ _ b c (hp s (by omega))))
  have hz : ∀ q ≤ T, (D q).zetaBar b c=(D 0).zetaBar b c := by
    intro q hq
    apply le_antisymm
    · have hh : (D q).zetaBar b c ≤ (D T).zetaBar b c := hmono hq (by simp) hq
      simpa [hcycle] using hh
    · exact hmono (Nat.zero_le _) hq (Nat.zero_le _)
  have hx : ∀ q ≤ T, (D q).bbar b=(D 0).bbar b := by
    intro q hq
    induction q with
    | zero => rfl
    | succ q ih =>
      exact (bl_pivot_same _ _ b c (bl_bland_simplex _ _ b c (hp q (by omega)))
        ((hz (q+1) hq).trans (hz q (by omega)).symm)).trans (ih (by omega))
  let F := Finset.univ.filter (fun j : Fin (n+m) =>
    (∃ q ≤ T, j ∈ (D q).B) ∧ (∃ q ≤ T, j ∉ (D q).B))
  have hF : F.Nonempty := by
    obtain ⟨k,l,hk,hl,hB⟩ := hp 0 hT
    refine ⟨k,?_⟩
    simp only [F,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨⟨1,by omega,hB ▸ Finset.mem_insert_self _ _⟩,⟨0,by omega,hk.1.1⟩⟩
  obtain ⟨t,ht,htmax⟩ := Finset.exists_max_image F id hF
  have htf := (Finset.mem_filter.mp ht).2
  obtain ⟨q,hq,htq,htqn⟩ := bl_cycle_leave (fun r => t ∈ (D r).B) T
    (by rw [hcycle]) htf.1 htf.2
  obtain ⟨r,hr,htnr,htrn⟩ := bl_cycle_enter (fun r => t ∈ (D r).B) T
    (by rw [hcycle]) htf.1 htf.2
  obtain ⟨k,l,hk,hl,hB⟩ := hp q hq
  have hlt : l=t := by
    by_contra hlt
    exact htqn (hB ▸ Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hlt,htq⟩))
  subst l
  obtain ⟨e,a,he,ha,hBr⟩ := hp r hr
  have het : e=t := by
    rw [hBr,Finset.mem_insert,Finset.mem_erase] at htrn
    exact htrn.resolve_right (fun h => htnr h.2) |>.symm
  subst e
  have hkn : k ∉ (D q).B := hk.1.1
  have hkt : k ≠ t := fun h => hkn (h ▸ htq)
  have hkF : k ∈ F := by
    simp only [F,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨⟨q+1,by omega,hB ▸ Finset.mem_insert_self _ _⟩,⟨q,by omega,hkn⟩⟩
  have hkle : k ≤ t := htmax k hkF
  have hkl : k < t := lt_of_le_of_ne hkle hkt
  have hzero : ∀ j ∈ F, (D q).bbar b j=0 := by
    intro j hj
    obtain ⟨s,hs,hjs⟩ := (Finset.mem_filter.mp hj).2.2
    rw [hx q hq.le,← hx s hs]
    exact bl_bbar_not _ b hjs
  have hdir_nonneg : ∀ j, j < t → j ∉ (D r).B → 0 ≤ bl_dir (D q) k j := by
    intro j hj hjr
    by_cases hjk : j=k
    · subst j
      rw [bl_dir_self _ hkn]
      norm_num
    · rw [bl_dir_other _ hjk]
      apply neg_nonneg.mpr
      by_contra haj
      have haj' : 0 < (D q).abar j k := lt_of_not_ge haj
      have hjq : j ∈ (D q).B := by
        by_contra hjq
        simpa [bl_abar_not _ hjq] using haj'
      have hjF : j ∈ F := by
        simp only [F,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨⟨q,hq.le,hjq⟩,⟨r,hr.le,hjr⟩⟩
      have hjcand : (D q).IsLeavingCandidate b k j := by
        refine ⟨hjq,haj',?_⟩
        intro i hi hai
        rw [hzero j hjF,zero_div]
        exact div_nonneg (hfeas q hq.le i hi) hai.le
      exact (not_le_of_gt hj) (hl.2 j hjcand)
  have hdir_zero : ∀ j, t < j → j ∉ (D r).B → bl_dir (D q) k j=0 := by
    intro j hj hjr
    have hjk : j ≠ k := by omega
    rw [bl_dir_other _ hjk]
    have hjq : j ∉ (D q).B := by
      intro hjq
      have hjF : j ∈ F := by
        simp only [F,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨⟨q,hq.le,hjq⟩,⟨r,hr.le,hjr⟩⟩
      exact (not_le_of_gt hj) (htmax j hjF)
    simp [bl_abar_not _ hjq]
  have hcost : (D q).cbar c k = ∑ j, (D r).cbar c j*bl_dir (D q) k j := by
    have hh := bl_cost_eq (D r) (extCost c) (bl_dir (D q) k) 0 (bl_dir_col _ _)
    simp only [bl_bbar_zero,mul_zero,Finset.sum_const_zero,zero_add] at hh
    rw [bl_dir_cost] at hh
    exact hh
  have hnonpos : ∀ j : Fin (n+m), (D r).cbar c j*bl_dir (D q) k j ≤ 0 := by
    intro j
    by_cases hjr : j ∈ (D r).B
    · simp [bl_cbar_basic _ c hjr]
    rcases lt_trichotomy j t with hj | rfl | hj
    · have hcj : (D r).cbar c j ≤ 0 := by
        by_contra hcj
        exact (not_le_of_gt hj) (he.2 j ⟨hjr,lt_of_not_ge hcj⟩)
      exact mul_nonpos_of_nonpos_of_nonneg hcj (hdir_nonneg j hj hjr)
    · rw [bl_dir_other _ (Ne.symm hkt)]
      exact mul_nonpos_of_nonneg_of_nonpos he.1.2.le (neg_nonpos.mpr hl.1.2.1.le)
    · simp [hdir_zero j hj hjr]
  have hsum := Finset.sum_nonpos (fun j (_ : j ∈ Finset.univ) => hnonpos j)
  rw [← hcost] at hsum
  exact (not_le_of_gt hk.1.2) hsum

end
end VanderbeiLP.Simplex


namespace VanderbeiLP.Simplex
noncomputable section
variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}

lemma bl_no_infinite (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (D₀ : Dictionary A) (h0 : D₀.IsFeasible b) :
    ¬ ∃ D : ℕ → Dictionary A, D 0=D₀ ∧ ∀ t, (D t).IsBlandPivot b c (D (t+1)) := by
  rintro ⟨D,hD,hstep⟩
  have hfeas : ∀ t, (D t).IsFeasible b := by
    intro t
    induction t with
    | zero => simpa [hD] using h0
    | succ t ih => exact bl_simplex_feasible _ _ b c ih (bl_bland_simplex _ _ b c (hstep t))
  obtain ⟨s,t,hst,heq⟩ := nonterminating_implies_cycling A b c D (hfeas 0)
    (fun t => bl_bland_simplex _ _ b c (hstep t))
  apply bl_no_bland_cycle (fun q => D (s+q)) b c (t-s) (by omega) ?_ ?_ ?_
  · simp only [Nat.add_zero]
    have hst' : s+(t-s)=t := by omega
    rw [hst',heq]
  · simpa using hfeas s
  · intro q hq
    simpa [Nat.add_assoc] using hstep (s+q)

lemma bl_terminates (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (D₀ : Dictionary A) (h0 : D₀.IsFeasible b) :
    (¬ ∃ D : ℕ → Dictionary A, D 0=D₀ ∧ ∀ t, (D t).IsBlandPivot b c (D (t+1))) ∧
    ∃ (T : ℕ) (D : ℕ → Dictionary A), D 0=D₀ ∧
      (∀ t<T, (D t).IsBlandPivot b c (D (t+1))) ∧ (D T).IsBlandTerminal c := by
  classical
  have hno := bl_no_infinite A b c D₀ h0
  refine ⟨hno,?_⟩
  let f (E : Dictionary A) : Dictionary A :=
    if h : ¬ E.IsBlandTerminal c then (bl_next E b c h).choose else E
  let D : ℕ → Dictionary A := Nat.rec D₀ (fun _ E => f E)
  have hD : D 0=D₀ := rfl
  have hsucc (t : ℕ) : D (t+1)=f (D t) := rfl
  have hp (t : ℕ) (ht : ¬ (D t).IsBlandTerminal c) :
      (D t).IsBlandPivot b c (D (t+1)) := by
    rw [hsucc]
    dsimp only [f]
    rw [dif_pos ht]
    exact (bl_next _ b c ht).choose_spec
  have hex : ∃ T, (D T).IsBlandTerminal c := by
    by_contra h
    apply hno
    exact ⟨D,hD,fun t => hp t (fun ht => h ⟨t,ht⟩)⟩
  refine ⟨Nat.find hex,D,hD,?_,Nat.find_spec hex⟩
  intro t ht
  exact hp t (Nat.find_min hex ht)

end
end VanderbeiLP.Simplex


namespace VanderbeiLP.Simplex
open Module Finset
noncomputable section

def bl_support {ι : Type*} [Fintype ι] (z : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => z i ≠ 0)

lemma bl_small_support {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (v : ι → V) (w : V) (hex : ∃ z : ι → ℝ, (∀ i, 0 ≤ z i) ∧ ∑ i, z i • v i=w) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i) ∧ (∑ i, z i • v i=w) ∧
      LinearIndependent ℝ (fun i : bl_support z => v i) := by
  classical
  let S : Set (ι → ℝ) := {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i • v i=w}
  have hS : S.Nonempty := hex
  let z := Function.argminOn (fun z : ι → ℝ => (bl_support z).card) S hS
  have hz : (∀ i, 0 ≤ z i) ∧ ∑ i, z i • v i=w :=
    Function.argminOn_mem _ S hS
  have hmin : ∀ z' ∈ S, (bl_support z).card ≤ (bl_support z').card := by
    intro z' hz'
    exact Function.argminOn_le (fun z : ι → ℝ => (bl_support z).card) S hz'
  refine ⟨z,hz.1,hz.2,?_⟩
  by_contra hn
  have hn' : ¬ LinearIndepOn ℝ v (↑(bl_support z) : Set ι) := hn
  rw [linearIndepOn_finset_iff] at hn'
  push_neg at hn'
  obtain ⟨r,hr,i,hi,hri⟩ := hn'
  let d₀ : ι → ℝ := fun j => if j ∈ bl_support z then r j else 0
  have hd₀ : ∑ j, d₀ j • v j=0 := by
    calc
      _ = ∑ j ∈ bl_support z, r j • v j := by
        rw [← Finset.sum_subset (Finset.subset_univ (bl_support z))
          (fun j _ hj => by simp [d₀,hj])]
        apply Finset.sum_congr rfl
        intro j hj
        simp [d₀,hj]
      _ = 0 := hr
  let d : ι → ℝ := if 0 < r i then d₀ else -d₀
  have hd : ∑ j, d j • v j=0 := by
    by_cases h : 0 < r i
    · simpa [d,h] using hd₀
    · simp only [d,if_neg h,Pi.neg_apply,neg_smul,Finset.sum_neg_distrib,hd₀,neg_zero]
  have hdi : 0 < d i := by
    by_cases h : 0 < r i
    · simpa [d,h,d₀,hi] using h
    · have h' : r i < 0 := lt_of_le_of_ne (le_of_not_gt h) hri
      simpa [d,h,d₀,hi] using neg_pos.mpr h'
  have hdnot : ∀ j ∉ bl_support z, d j=0 := by
    intro j hj
    by_cases h : 0 < r i <;> simp [d,h,d₀,hj]
  let P := Finset.univ.filter (fun j => 0 < d j)
  have hP : P.Nonempty := ⟨i,by simp [P,hdi]⟩
  obtain ⟨l,hl,hlmin⟩ := Finset.exists_min_image P (fun j => z j/d j) hP
  have hdl : 0 < d l := (Finset.mem_filter.mp hl).2
  have hlz : l ∈ bl_support z := by
    by_contra h
    simpa [hdnot l h] using hdl
  have hzl : 0 < z l := lt_of_le_of_ne (hz.1 l)
    (Ne.symm (Finset.mem_filter.mp hlz).2)
  let θ := z l/d l
  have hθ : 0 < θ := div_pos hzl hdl
  let z' : ι → ℝ := z-θ • d
  have hz' : ∀ j, 0 ≤ z' j := by
    intro j
    change 0 ≤ z j-θ*d j
    by_cases hj : 0 < d j
    · have hh := hlmin j (by simp [P,hj])
      have hh' := (le_div_iff₀ hj).mp hh
      exact sub_nonneg.mpr hh'
    · have hh : θ*d j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ.le (le_of_not_gt hj)
      linarith [hz.1 j]
  have hcol : ∑ j, z' j • v j=w := by
    simp only [z',Pi.sub_apply,Pi.smul_apply,smul_eq_mul,sub_smul,mul_smul,
      Finset.sum_sub_distrib,← Finset.smul_sum,hd,smul_zero,sub_zero,hz.2]
  have hsubset : bl_support z' ⊆ bl_support z := by
    intro j hj
    by_contra h
    have hzj : z j=0 := by simpa [bl_support] using h
    have hzj' : z' j=0 := by simp [z',hzj,hdnot j h]
    exact (Finset.mem_filter.mp hj).2 hzj'
  have hlnot : l ∉ bl_support z' := by
    have hzero : z' l=0 := by
      change z l-(z l/d l)*d l=0
      field_simp [hdl.ne']
      ring
    simp [bl_support,hzero]
  have hss : bl_support z' ⊂ bl_support z :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsubset,fun h => hlnot (h.symm ▸ hlz)⟩
  exact (not_le_of_gt (Finset.card_lt_card hss)) (hmin z' ⟨hz',hcol⟩)

variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}

lemma bl_aug_sum (z : Fin (n+m) → ℝ) :
    ∑ j, z j • augCol A j = fun i => (∑ j, A i j*z (Fin.castAdd m j)) + z (Fin.natAdd n i) := by
  classical
  rw [Fin.sum_univ_add]
  ext i
  simp [augCol,Finset.sum_apply,Pi.single_apply,mul_comm]

lemma bl_slacks_col (b : Fin m → ℝ) (x : Fin n → ℝ) :
    ∑ j, withSlacks A b x j • augCol A j=b := by
  rw [bl_aug_sum]
  ext i
  simp [withSlacks]

lemma bl_aug_solution (b : Fin m → ℝ) (z : Fin (n+m) → ℝ)
    (hz : ∀ j, 0 ≤ z j) (hcol : ∑ j, z j • augCol A j=b) :
    let x : Fin n → ℝ := fun j => z (Fin.castAdd m j)
    IsFeasibleSol A b x ∧ withSlacks A b x=z := by
  classical
  dsimp only
  have he := congrFun (bl_aug_sum (A := A) z |>.symm.trans hcol)
  refine ⟨⟨?_,fun j => hz _⟩,?_⟩
  · intro i
    have hh := he i
    linarith [hz (Fin.natAdd n i)]
  · ext j
    refine Fin.addCases (fun k => ?_) (fun i => ?_) j
    · simp [withSlacks]
    · have hh := he i
      simp only [withSlacks,Fin.append_right]
      linarith

lemma bl_aug_span : Submodule.span ℝ (Set.range (augCol A))=⊤ := by
  apply top_unique
  intro v _
  have he : v = ∑ i : Fin m, v i • augCol A (Fin.natAdd n i) := by
    ext j
    simp [augCol,Finset.sum_apply,Pi.single_apply]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.natAdd n i,rfl⟩)

lemma bl_extend_basis (S : Finset (Fin (n+m)))
    (hS : LinearIndependent ℝ (fun i : S => augCol A i)) :
    ∃ D : Dictionary A, S ⊆ D.B := by
  classical
  obtain ⟨B,hBu,hSB,hspan,hli⟩ := exists_linearIndepOn_extension
    (show LinearIndepOn ℝ (augCol A) (↑S : Set (Fin (n+m))) from hS) (Set.subset_univ _)
  let T := B.toFinset
  have hT : LinearIndependent ℝ (fun i : T => augCol A i) := by
    change LinearIndepOn ℝ (augCol A) (↑T : Set (Fin (n+m)))
    simpa only [T,Set.coe_toFinset] using hli
  have hsp : Submodule.span ℝ (Set.range (fun i : T => augCol A i))=⊤ := by
    apply top_unique
    rw [← bl_aug_span (A := A)]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    have hh := hspan (show augCol A j ∈ augCol A '' Set.univ from ⟨j,Set.mem_univ _,rfl⟩)
    have he : Set.range (fun i : T => augCol A i)=augCol A '' B := by
      ext v
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨i,Set.mem_toFinset.mp i.property,rfl⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,Set.mem_toFinset.mpr hi⟩,rfl⟩
    rw [he]
    exact hh
  let e : Basis T ℝ (Fin m → ℝ) := Basis.mk hT hsp.ge
  have hc : T.card=m := by
    have hh := Module.finrank_eq_card_basis e
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,Fintype.card_coe] using hh.symm
  refine ⟨⟨T,hc,hT⟩,?_⟩
  intro i hi
  exact Set.mem_toFinset.mpr (hSB hi)

lemma bl_feasible_dictionary (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hex : ∃ x, IsFeasibleSol A b x) : ∃ D : Dictionary A, D.IsFeasible b := by
  classical
  obtain ⟨x,hx⟩ := hex
  have hxnon : ∀ j, 0 ≤ withSlacks A b x j := by
    intro j
    refine Fin.addCases (fun k => ?_) (fun i => ?_) j
    · simpa [withSlacks] using hx.2 k
    · simpa [withSlacks] using sub_nonneg.mpr (hx.1 i)
  obtain ⟨z,hz,hcol,hli⟩ := bl_small_support (augCol A) b ⟨withSlacks A b x,hxnon,bl_slacks_col b x⟩
  obtain ⟨D,hD⟩ := bl_extend_basis (bl_support z) hli
  have he : z=D.bbar b := bl_unique D z b hcol (fun j hj => by
    by_contra h
    exact hj (hD (by simp [bl_support,h])))
  refine ⟨D,?_⟩
  intro i hi
  rw [← he]
  exact hz i

end
end VanderbeiLP.Simplex


namespace VanderbeiLP.Simplex
open Finset
noncomputable section
variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}

lemma bl_slacks_nonneg (b : Fin m → ℝ) (x : Fin n → ℝ) (hx : IsFeasibleSol A b x) :
    ∀ j, 0 ≤ withSlacks A b x j := by
  intro j
  refine Fin.addCases (fun k => ?_) (fun i => ?_) j
  · simpa [withSlacks] using hx.2 k
  · simpa [withSlacks] using sub_nonneg.mpr (hx.1 i)

lemma bl_bbar_nonneg (D : Dictionary A) (b : Fin m → ℝ) (hD : D.IsFeasible b) :
    ∀ j, 0 ≤ D.bbar b j := by
  intro j
  by_cases hj : j ∈ D.B
  · exact hD j hj
  · rw [bl_bbar_not D b hj]

lemma bl_aug_cost (c : Fin n → ℝ) (z : Fin (n+m) → ℝ) :
    ∑ j, extCost c j*z j = objective c (fun j => z (Fin.castAdd m j)) := by
  rw [Fin.sum_univ_add]
  simp [extCost,objective]

lemma bl_zeta_cost (D : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    ∑ j, extCost c j*D.bbar b j=D.zetaBar b c := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  simp [bl_bbar_not D b hj]

lemma bl_basic_feasible (D : Dictionary A) (b : Fin m → ℝ) (hD : D.IsFeasible b) :
    IsBasicFeasibleSol A b (fun j => D.bbar b (Fin.castAdd m j)) := by
  obtain ⟨hx,he⟩ := bl_aug_solution b (D.bbar b) (bl_bbar_nonneg D b hD) (bl_repr_all D b)
  exact ⟨hx,D,he⟩

lemma bl_no_enter_optimal (D : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hD : D.IsFeasible b) (hn : ∀ j, ¬ D.IsEnteringCandidate c j) :
    IsBasicOptimalSol A b c (fun j => D.bbar b (Fin.castAdd m j)) := by
  classical
  have hx := bl_basic_feasible D b hD
  refine ⟨⟨hx.1,?_⟩,hx.2⟩
  intro y hy
  have hc : ∀ j, D.cbar c j ≤ 0 := by
    intro j
    by_cases hj : j ∈ D.B
    · simp [bl_cbar_basic D c hj]
    · exact le_of_not_gt (fun h => hn j ⟨hj,h⟩)
  have hh := bl_cost_eq D (extCost c) (withSlacks A b y) b (bl_slacks_col b y)
  have hnn : (∑ j, D.cbar c j*withSlacks A b y j) ≤ 0 :=
    Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hc j) (bl_slacks_nonneg b y hy j))
  rw [bl_aug_cost] at hh
  have he : (fun j => withSlacks A b y (Fin.castAdd m j))=y := by ext j; simp [withSlacks]
  rw [he] at hh
  have hval : objective c (fun j => D.bbar b (Fin.castAdd m j))=D.zetaBar b c :=
    (bl_aug_cost c (D.bbar b)).symm.trans (bl_zeta_cost D b c)
  rw [hval]
  change objective c y=D.zetaBar b c+∑ j, D.cbar c j*withSlacks A b y j at hh
  linarith

lemma bl_unbounded_column (D : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hD : D.IsFeasible b) {k : Fin (n+m)} (hk : D.IsEnteringCandidate c k)
    (ha : ∀ i ∈ D.B, D.abar i k ≤ 0) : IsUnbounded A b c := by
  classical
  have hdir : ∀ j, 0 ≤ bl_dir D k j := by
    intro j
    by_cases hj : j=k
    · subst j
      rw [bl_dir_self D hk.1]
      norm_num
    · rw [bl_dir_other D hj]
      apply neg_nonneg.mpr
      by_cases hjB : j ∈ D.B
      · exact ha j hjB
      · simp [bl_abar_not D hjB]
  intro M
  let θ := (|M|+|D.zetaBar b c|+1)/D.cbar c k
  have hθ : 0 < θ := div_pos (by positivity) hk.2
  let z := D.bbar b+θ • bl_dir D k
  have hz : ∀ j, 0 ≤ z j := by
    intro j
    exact add_nonneg (bl_bbar_nonneg D b hD j) (mul_nonneg hθ.le (hdir j))
  have hcol : ∑ j, z j • augCol A j=b := by
    simp only [z,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_smul,mul_smul,
      Finset.sum_add_distrib,← Finset.smul_sum,bl_repr_all,bl_dir_col,smul_zero,add_zero]
  obtain ⟨hx,he⟩ := bl_aug_solution b z hz hcol
  refine ⟨fun j => z (Fin.castAdd m j),hx,?_⟩
  rw [← bl_aug_cost]
  have hcost : (∑ j, extCost c j*z j)=D.zetaBar b c+θ*D.cbar c k := by
    simp only [z,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
    rw [bl_zeta_cost]
    have hsum : (∑ j, extCost c j*(θ*bl_dir D k j))=θ*(∑ j, extCost c j*bl_dir D k j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum,bl_dir_cost]
  rw [hcost]
  have hmul : θ*D.cbar c k=|M|+|D.zetaBar b c|+1 := by
    dsimp only [θ]
    field_simp [hk.2.ne']
  rw [hmul]
  linarith [le_abs_self M,neg_abs_le (D.zetaBar b c)]

lemma bl_terminal_outcome (D : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hD : D.IsFeasible b) (ht : D.IsBlandTerminal c) :
    (∃ x, IsBasicOptimalSol A b c x) ∨ IsUnbounded A b c := by
  rcases ht with hn | ⟨k,hk,ha⟩
  · exact Or.inl ⟨_,bl_no_enter_optimal D b c hD hn⟩
  · exact Or.inr (bl_unbounded_column D b c hD hk.1 ha)

lemma bl_finite_outcome (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hex : ∃ x, IsFeasibleSol A b x) :
    (∃ x, IsBasicOptimalSol A b c x) ∨ IsUnbounded A b c := by
  obtain ⟨D₀,h0⟩ := bl_feasible_dictionary A b hex
  obtain ⟨T,D,hD,hp,ht⟩ := (bl_terminates A b c D₀ h0).2
  have hfeas : ∀ t ≤ T, (D t).IsFeasible b := by
    intro t ht
    induction t with
    | zero => simpa [hD] using h0
    | succ t ih =>
      exact bl_simplex_feasible _ _ b c (ih (by omega))
        (bl_bland_simplex _ _ b c (hp t (by omega)))
  exact bl_terminal_outcome (D T) b c (hfeas T le_rfl) ht

lemma bl_fundamental (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    ((¬ ∃ x, IsOptimalSol A b c x) → IsInfeasible A b ∨ IsUnbounded A b c) ∧
    ((∃ x, IsFeasibleSol A b x) → ∃ x, IsBasicFeasibleSol A b x) ∧
    ((∃ x, IsOptimalSol A b c x) → ∃ x, IsBasicOptimalSol A b c x) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro hn
    by_cases hex : ∃ x, IsFeasibleSol A b x
    · rcases bl_finite_outcome A b c hex with ⟨x,hx⟩ | hu
      · exact (hn ⟨x,hx.1⟩).elim
      · exact Or.inr hu
    · exact Or.inl (fun x hx => hex ⟨x,hx⟩)
  · intro hex
    obtain ⟨D,hD⟩ := bl_feasible_dictionary A b hex
    exact ⟨_,bl_basic_feasible D b hD⟩
  · rintro ⟨x,hx⟩
    rcases bl_finite_outcome A b c ⟨x,hx.1⟩ with ho | hu
    · exact ho
    · obtain ⟨y,hy,hlt⟩ := hu (objective c x)
      exact (not_lt_of_ge (hx.2 y hy) hlt).elim

end
end VanderbeiLP.Simplex

open VanderbeiLP.Simplex

/-- **Vanderbei, Theorem 3.4 (p. 33), fundamental theorem of linear programming.** For the
standard-form problem `maximize cᵀx s.t. Ax ≤ b, x ≥ 0`:
1. if there is no optimal solution, the problem is infeasible or unbounded;
2. if a feasible solution exists, a basic feasible solution exists;
3. if an optimal solution exists, a basic optimal solution exists. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) :
    ((¬ ∃ x, IsOptimalSol A b c x) → IsInfeasible A b ∨ IsUnbounded A b c) ∧
    ((∃ x, IsFeasibleSol A b x) → ∃ x, IsBasicFeasibleSol A b x) ∧
    ((∃ x, IsOptimalSol A b c x) → ∃ x, IsBasicOptimalSol A b c x) := by
  exact bl_fundamental A b c

#print axioms solution
