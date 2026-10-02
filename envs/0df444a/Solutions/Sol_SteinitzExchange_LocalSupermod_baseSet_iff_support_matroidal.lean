-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.baseSet_iff_support_matroidal
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T23:18:32.245978+00:00
-- url     : https://prove2.me/submissions/d3cc98d3-b194-4b41-86e5-92d41ac5edb9

import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Theorems.Thm_SteinitzExchange_Duality_baseSet_iff_submodular_system
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false

/- Component: Solutions/SteinitzLocalSupport.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SteinitzLocalRepair

open SteinitzExchange.LocalSupermod

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma supportMin_le_pairing (B : Finset (V → ℤ)) (p : V → ℝ)
    {x : V → ℤ} (hx : x ∈ B) : supportMin B p ≤ pairing p (toReal x) :=
  ciInf_le (Set.finite_range (fun a : (B : Set (V → ℤ)) => pairing p (toReal a.val))).bddBelow ⟨x,hx⟩

lemma le_supportMin (B : Finset (V → ℤ)) (hne : B.Nonempty) (p : V → ℝ) (a : ℝ)
    (ha : ∀ x ∈ B, a ≤ pairing p (toReal x)) : a ≤ supportMin B p := by
  letI : Nonempty (B : Set (V → ℤ)) := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  exact le_ciInf (fun x => ha x.val x.property)

lemma supportMin_eq_of_minimum (B : Finset (V → ℤ)) (p : V → ℝ)
    {x : V → ℤ} (hx : x ∈ B) (hmin : ∀ y ∈ B, pairing p (toReal x) ≤ pairing p (toReal y)) :
    supportMin B p = pairing p (toReal x) :=
  le_antisymm (supportMin_le_pairing B p hx) (le_supportMin B ⟨x,hx⟩ p _ hmin)

lemma supportMin_attained (B : Finset (V → ℤ)) (hne : B.Nonempty) (p : V → ℝ) :
    ∃ x ∈ B, supportMin B p = pairing p (toReal x) := by
  classical
  obtain ⟨x,hx,hmin⟩ := Finset.exists_min_image B (fun x => pairing p (toReal x)) hne
  exact ⟨x,hx,supportMin_eq_of_minimum B p hx hmin⟩

lemma pairing_smul_left (c : ℝ) (p b : V → ℝ) :
    pairing (c • p) b = c * pairing p b := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma pairing_charVec (X : Finset V) (x : V → ℤ) :
    pairing (charVec X) (toReal x) = (sumOn x X : ℝ) := by
  simp [pairing,charVec,toReal,sumOn,Finset.sum_ite_mem]

lemma supportMin_posHomogeneous (B : Finset (V → ℤ)) (hne : B.Nonempty) :
    IsPosHomogeneous (supportMin B) := by
  intro c hc p
  obtain ⟨x,hx,heq⟩ := supportMin_attained B hne p
  rw [heq]
  rw [← pairing_smul_left]
  apply supportMin_eq_of_minimum B (c • p) hx
  intro y hy
  simp only [pairing_smul_left]
  exact mul_le_mul_of_nonneg_left (heq ▸ supportMin_le_pairing B p hy) hc.le

lemma supportMin_charVec (B : Finset (V → ℤ)) (hne : B.Nonempty) (X : Finset V) :
    supportMin B (charVec X) = ((B.inf' hne (fun x => sumOn x X) : ℤ) : ℝ) := by
  classical
  obtain ⟨x,hx,heq⟩ := B.exists_mem_eq_inf' hne (fun x => sumOn x X)
  rw [heq]
  rw [← pairing_charVec]
  apply supportMin_eq_of_minimum B (charVec X) hx
  intro y hy
  simp only [pairing_charVec]
  have h := B.inf'_le (fun x => sumOn x X) hy
  rw [heq] at h
  exact_mod_cast h

#print axioms supportMin_posHomogeneous
#print axioms supportMin_charVec

end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzChainTelescoping.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SteinitzLocalRepair

def chainCoefficient {n : ℕ} (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  p j - if hj : (j : ℕ) + 1 < n then p ⟨(j : ℕ) + 1, hj⟩ else 0

lemma next_lastCases {n : ℕ} (p : Fin n → ℝ) (j : Fin n) :
    Fin.lastCases (0 : ℝ) p j.succ =
      if hj : (j : ℕ) + 1 < n then p ⟨(j : ℕ) + 1, hj⟩ else 0 := by
  by_cases h : (j : ℕ) + 1 < n
  · rw [dif_pos h]
    have he : j.succ = (⟨(j : ℕ) + 1, h⟩ : Fin n).castSucc := by
      apply Fin.ext
      rfl
    rw [he, Fin.lastCases_castSucc]
  · rw [dif_neg h]
    have he : j.succ = Fin.last n := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    rw [he, Fin.lastCases_last]

lemma chainCoefficient_suffix {n : ℕ} (p : Fin n → ℝ) (i : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j => i ≤ j), chainCoefficient p j) = p i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hs : Finset.univ.filter (fun j : Fin (n+1) => i ≤ j) =
        Finset.Icc i (Fin.last n) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Icc]
      exact ⟨fun h => ⟨h,Fin.le_last j⟩, fun h => h.1⟩
    rw [hs]
    let q : Fin (n+2) → ℝ := fun j => Fin.lastCases (0 : ℝ) p j
    have ht := Fin.sum_Icc_sub (M := ℝ) (Fin.le_last i)
      (fun j : Fin (n+2) => -(q j))
    calc
      (∑ j ∈ Finset.Icc i (Fin.last n), chainCoefficient p j) =
          ∑ j ∈ Finset.Icc i (Fin.last n),
            ((-(q j.succ)) - (-(q j.castSucc))) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [q]
        rw [Fin.lastCases_castSucc, next_lastCases]
        simp only [chainCoefficient]
        ring
      _ = p i := by simpa [q] using ht

lemma weighted_chain_expansion {n : ℕ} (p x : Fin n → ℝ) :
    (∑ i, p i * x i) =
      ∑ j, chainCoefficient p j * ∑ i ∈ Finset.univ.filter (fun i => i ≤ j), x i := by
  classical
  symm
  simp only [Finset.sum_filter, Finset.mul_sum]
  calc
    (∑ j, ∑ i, chainCoefficient p j * (if i ≤ j then x i else 0)) =
        ∑ i, ∑ j, if i ≤ j then chainCoefficient p j * x i else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = ∑ i, p i * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter, ← Finset.sum_mul, chainCoefficient_suffix]

#print axioms chainCoefficient_suffix
#print axioms weighted_chain_expansion

end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzLocalChainCore.lean -/
section

set_option autoImplicit false
open scoped BigOperators
open SteinitzExchange.Extension

namespace SteinitzLocalRepairChain

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def positiveDeviation (x y : V → ℤ) : ℤ :=
  ∑ w, max (x w - y w) 0

theorem positiveDeviation_exchange (x y : V → ℤ) (u v : V)
    (hu : 0 < (x - y) u) (hv : (x - y) v < 0) :
    positiveDeviation (x - chi u + chi v) y = positiveDeviation x y - 1 := by
  have huv : u ≠ v := by
    intro h
    subst v
    omega
  have hpoint : ∀ w, max ((x - chi u + chi v) w - y w) 0 =
      max (x w - y w) 0 - (if w = u then 1 else 0) := by
    intro w
    by_cases hwu : w = u
    · subst w
      simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
        if_pos rfl, if_neg huv, sub_self]
      change 0 < x u - y u at hu
      omega
    · by_cases hwv : w = v
      · subst w
        simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
          if_pos rfl, if_neg hwu, sub_zero]
        change x v - y v < 0 at hv
        omega
      · simp [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply, hwu, hwv]
  simp only [positiveDeviation, hpoint, Finset.sum_sub_distrib]
  simp

/-- Constant totals from the public base-polytope characterization. -/
theorem base_sum_eq {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B) :
    (∑ v, x v) = ∑ v, y v := by
  obtain ⟨f,hf,hf0,hrep⟩ :=
    (SteinitzExchange.Duality.baseSet_iff_submodular_system B hB.1).1.mp hB
  have hxsum := ((hrep x).mp hx).2
  have hysum := ((hrep y).mp hy).2
  exact hxsum.trans hysum.symm

def coordSum (S : Finset V) (x : V → ℤ) : ℤ := ∑ i ∈ S, x i

lemma coordSum_exchange (S : Finset V) (x : V → ℤ) (u v : V) :
    coordSum S (x - chi u + chi v) =
      coordSum S x - (if u ∈ S then 1 else 0) + (if v ∈ S then 1 else 0) := by
  simp [coordSum, Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma exists_surplus_outside {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B) (U : Finset V)
    (hlt : coordSum U x < coordSum U y) :
    ∃ i, i ∉ U ∧ 0 < (x-y) i := by
  by_contra hn
  have hcomp : (∑ i ∈ Uᶜ, x i) ≤ ∑ i ∈ Uᶜ, y i := by
    apply Finset.sum_le_sum
    intro i hi
    have hiU : i ∉ U := Finset.mem_compl.mp hi
    by_contra hnot
    apply hn
    refine ⟨i,hiU,?_⟩
    change 0 < x i - y i
    omega
  have ht := base_sum_eq hB hx hy
  have hcx := Finset.sum_add_sum_compl U (fun i => x i)
  have hcy := Finset.sum_add_sum_compl U (fun i => y i)
  unfold coordSum at hlt
  omega

/-- Extend a previously feasible family of tight maxima by a containing set. -/
theorem extend_sum_maximizers {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (C : Finset (Finset V)) (U : Finset V) (hCU : ∀ T ∈ C, T ⊆ U)
    (hprior : ∃ z ∈ B, ∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T z) :
    ∃ x ∈ B, (∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T x) ∧
      (∀ a ∈ B, coordSum U a ≤ coordSum U x) := by
  classical
  obtain ⟨z,hz,hzmax⟩ := hprior
  obtain ⟨y,hy,hymax⟩ := Finset.exists_max_image B (coordSum U) hB.1
  let S := B.filter (fun x => ∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T x)
  have hS : S.Nonempty := ⟨z,Finset.mem_filter.mpr ⟨hz,hzmax⟩⟩
  obtain ⟨x,hxS,hmin⟩ := Finset.exists_min_image S
    (fun x => positiveDeviation x y) hS
  have hx : x ∈ B := (Finset.mem_filter.mp hxS).1
  have hxmax := (Finset.mem_filter.mp hxS).2
  have hxU : coordSum U x = coordSum U y := by
    by_contra hne
    have hlt : coordSum U x < coordSum U y := by
      have := hymax x hx
      omega
    obtain ⟨u,huU,hu⟩ := exists_surplus_outside hB hx hy U hlt
    obtain ⟨v,hv,hx'⟩ := hB.2 x hx y hy u hu
    have heq : ∀ T ∈ C, coordSum T (x-chi u+chi v) = coordSum T x := by
      intro T hT
      have huT : u ∉ T := fun h => huU (hCU T hT h)
      have hvT : v ∉ T := by
        intro hvT
        have hh := hxmax T hT (x-chi u+chi v) hx'
        rw [coordSum_exchange,if_neg huT,if_pos hvT] at hh
        omega
      rw [coordSum_exchange,if_neg huT,if_neg hvT]
      simp
    have hmem : x-chi u+chi v ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨hx',?_⟩
      intro T hT a ha
      rw [heq T hT]
      exact hxmax T hT a ha
    have hm := hmin _ hmem
    rw [positiveDeviation_exchange x y u v hu hv] at hm
    omega
  refine ⟨x,hx,hxmax,?_⟩
  intro a ha
  rw [hxU]
  exact hymax a ha

/-- Every finite inclusion chain has a common rank-maximizing base. -/
theorem chain_sum_maximizers {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (C : Finset (Finset V))
    (hchain : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T) :
    ∃ x ∈ B, ∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T x := by
  classical
  revert hchain
  refine Finset.strongInductionOn C ?_
  intro C ih hchain
  by_cases hC : C.Nonempty
  · obtain ⟨U,hU,hUmax⟩ := Finset.exists_max_image C Finset.card hC
    have hall : ∀ T ∈ C, T ⊆ U := by
      intro T hT
      rcases hchain T hT U hU with h | h
      · exact h
      · have heq : U = T := Finset.eq_of_subset_of_card_le h (hUmax T hT)
        exact heq.symm.subset
    obtain ⟨z,hz,hzmax⟩ := ih (C.erase U) (Finset.erase_ssubset hU)
      (fun T hT W hW => hchain T (Finset.mem_of_mem_erase hT) W
        (Finset.mem_of_mem_erase hW))
    obtain ⟨x,hx,hxmax,hxU⟩ := extend_sum_maximizers hB (C.erase U) U
      (fun T hT => hall T (Finset.mem_of_mem_erase hT)) ⟨z,hz,hzmax⟩
    refine ⟨x,hx,?_⟩
    intro T hT a ha
    by_cases hTU : T = U
    · subst T
      exact hxU a ha
    · exact hxmax T (Finset.mem_erase.mpr ⟨hTU,hT⟩) a ha
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hC
    obtain ⟨x,hx⟩ := hB.1
    exact ⟨x,hx,by simp⟩

#print axioms chain_sum_maximizers

end SteinitzLocalRepairChain
end

/- Component: Solutions/SteinitzChainMinimizers.lean -/
section

set_option autoImplicit false

namespace SteinitzLocalRepair

open SteinitzExchange.Extension SteinitzLocalRepairChain

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Complementing a finite inclusion chain converts simultaneous maxima to minima,
since every two members of an integral base set have the same total sum. -/
theorem chain_sum_minimizers {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (C : Finset (Finset V))
    (hchain : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T) :
    ∃ x ∈ B, ∀ T ∈ C, ∀ a ∈ B, coordSum T x ≤ coordSum T a := by
  classical
  let D : Finset (Finset V) := C.image (fun T => Tᶜ)
  have hD : ∀ T ∈ D, ∀ U ∈ D, T ⊆ U ∨ U ⊆ T := by
    intro T hT U hU
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hU
    rcases hchain S hS R hR with h | h
    · right
      intro v hv
      exact Finset.mem_compl.mpr (fun hvS => Finset.mem_compl.mp hv (h hvS))
    · left
      intro v hv
      exact Finset.mem_compl.mpr (fun hvR => Finset.mem_compl.mp hv (h hvR))
  obtain ⟨x,hx,hmax⟩ := chain_sum_maximizers hB D hD
  refine ⟨x,hx,?_⟩
  intro T hT a ha
  have hcomp := hmax Tᶜ (Finset.mem_image.mpr ⟨T,hT,rfl⟩) a ha
  have htotal := SteinitzLocalRepairChain.base_sum_eq hB hx ha
  have hcx := Finset.sum_add_sum_compl T (fun v => x v)
  have hca := Finset.sum_add_sum_compl T (fun v => a v)
  unfold coordSum at hcomp ⊢
  omega

#print axioms chain_sum_minimizers

end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzLocalForward.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SteinitzLocalRepair

open SteinitzExchange.LocalSupermod

variable {V : Type*} [Fintype V] [DecidableEq V]

def chainPrefix (σ : Fin (Fintype.card V) ≃ V) (j : Fin (Fintype.card V)) : Finset V :=
  Finset.univ.filter (fun v => σ.symm v ≤ j)

lemma chainPrefix_mono (σ : Fin (Fintype.card V) ≃ V)
    {i j : Fin (Fintype.card V)} (hij : i ≤ j) : chainPrefix σ i ⊆ chainPrefix σ j := by
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.trans hij⟩

lemma chainPrefix_terminal (σ : Fin (Fintype.card V) ≃ V)
    (j : Fin (Fintype.card V)) (hj : ¬ (j : ℕ) + 1 < Fintype.card V) :
    chainPrefix σ j = Finset.univ := by
  ext v
  simp only [chainPrefix,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
  apply Fin.le_def.mpr
  have hv := (σ.symm v).isLt
  have hj' := j.isLt
  omega

lemma indexed_prefix_sum (σ : Fin (Fintype.card V) ≃ V)
    (j : Fin (Fintype.card V)) (x : V → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => i ≤ j), x (σ i)) =
      ∑ v ∈ chainPrefix σ j, x v := by
  simp only [chainPrefix,Finset.sum_filter]
  simpa only [Equiv.symm_apply_apply] using
    σ.sum_comp (fun v => if σ.symm v ≤ j then x v else 0)

lemma pairing_chain_expansion (σ : Fin (Fintype.card V) ≃ V)
    (p : V → ℝ) (x : V → ℤ) :
    pairing p (toReal x) =
      ∑ j, chainCoefficient (p ∘ σ) j * (sumOn x (chainPrefix σ j) : ℝ) := by
  have h := weighted_chain_expansion (p ∘ σ) (fun i => (x (σ i) : ℝ))
  rw [show (∑ i, (p ∘ σ) i * (x (σ i) : ℝ)) = pairing p (toReal x) from
    by simpa only [Function.comp_apply,pairing,toReal] using
      σ.sum_comp (fun v => p v * (x v : ℝ))] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  rw [indexed_prefix_sum σ j (fun v => (x v : ℝ))]
  simp only [sumOn,Int.cast_sum]

lemma supportMin_satisfiesC1 [Nonempty V] (B : Finset (V → ℤ))
    (hB : IsIntegralBaseSet B) : SatisfiesC1 (supportMin B) := by
  obtain ⟨g,hg,hg0,hrep⟩ :=
    ((SteinitzExchange.Duality.baseSet_iff_submodular_system B hB.1).2.1).mp hB
  have hcanon := (SteinitzExchange.Duality.baseSet_iff_submodular_system B hB.1).2.2.2
    g hg hg0 hrep
  have hval (X : Finset V) : supportMin B (charVec X) = (g X : ℝ) := by
    rw [hcanon X]
    exact supportMin_charVec B hB.1 X
  intro X Y
  change supportMin B (charVec X) + supportMin B (charVec Y) ≤
    supportMin B (charVec (X ∪ Y)) + supportMin B (charVec (X ∩ Y))
  rw [hval X,hval Y,hval (X ∪ Y),hval (X ∩ Y)]
  exact_mod_cast hg X Y

lemma supportMin_satisfiesC2 [Nonempty V] (B : Finset (V → ℤ))
    (hB : IsIntegralBaseSet B) : SatisfiesC2 (supportMin B) := by
  classical
  intro p σ hp
  let C := Finset.univ.image (chainPrefix σ)
  have hchain : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T := by
    intro T hT U hU
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hU
    rcases le_total i j with hij | hji
    · exact Or.inl (chainPrefix_mono σ hij)
    · exact Or.inr (chainPrefix_mono σ hji)
  obtain ⟨x,hx,hmin⟩ := chain_sum_minimizers hB C hchain
  have hprefix (j : Fin (Fintype.card V)) (y : V → ℤ) (hy : y ∈ B) :
      sumOn x (chainPrefix σ j) ≤ sumOn y (chainPrefix σ j) :=
    hmin _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) y hy
  have hxopt : ∀ y ∈ B, pairing p (toReal x) ≤ pairing p (toReal y) := by
    intro y hy
    rw [pairing_chain_expansion σ p x,pairing_chain_expansion σ p y]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hnext : (j : ℕ) + 1 < Fintype.card V
    · have hcoeff : 0 ≤ chainCoefficient (p ∘ σ) j := by
        rw [chainCoefficient,dif_pos hnext]
        exact sub_nonneg.mpr (hp (show j ≤ ⟨(j : ℕ) + 1,hnext⟩ from
          Fin.le_def.mpr (Nat.le_succ _)))
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hprefix j y hy) hcoeff
    · rw [chainPrefix_terminal σ j hnext]
      have ht : sumOn x Finset.univ = sumOn y Finset.univ :=
        SteinitzLocalRepairChain.base_sum_eq hB hx hy
      rw [ht]
  have hchar (j : Fin (Fintype.card V)) :
      supportMin B (charVec (chainPrefix σ j)) = (sumOn x (chainPrefix σ j) : ℝ) := by
    rw [← pairing_charVec]
    apply supportMin_eq_of_minimum B _ hx
    intro y hy
    simp only [pairing_charVec]
    exact_mod_cast hprefix j y hy
  rw [supportMin_eq_of_minimum B p hx hxopt,pairing_chain_expansion σ p x]
  change (∑ j, chainCoefficient (p ∘ σ) j * (sumOn x (chainPrefix σ j) : ℝ)) =
    ∑ j, chainCoefficient (p ∘ σ) j * supportMin B (charVec (chainPrefix σ j))
  simp_rw [hchar]

theorem base_implies_support_matroidal [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) : IsMatroidal (supportMin B) :=
  ⟨supportMin_posHomogeneous B hB.1, supportMin_satisfiesC1 B hB, supportMin_satisfiesC2 B hB⟩

#print axioms pairing_chain_expansion
#print axioms base_implies_support_matroidal

end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzSortedIndexing.lean -/
section

set_option autoImplicit false

namespace SteinitzLocalRepair

/-- A descending indexing, including ties, for a finite real-valued vector. -/
theorem exists_antitone_indexing {V : Type*} [Fintype V] (p : V → ℝ) :
    ∃ σ : Fin (Fintype.card V) ≃ V, Antitone (p ∘ σ) := by
  classical
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let f : Fin (Fintype.card V) → ℝᵒᵈ := fun i => OrderDual.toDual (p (e i))
  refine ⟨(Tuple.sort f).trans e, ?_⟩
  change Monotone (f ∘ Tuple.sort f)
  exact Tuple.monotone_sort f

#print axioms exists_antitone_indexing

end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzLocalSupportConverse.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SteinitzLocalRepair
open SteinitzExchange.LocalSupermod
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma linear_map_coordinates (f : (V → ℝ) →ₗ[ℝ] ℝ) (z : V → ℝ) :
    f z = ∑ i, f (Pi.single i 1) * z i := by
  have hz : z = ∑ i, z i • (Pi.single i 1 : V → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]
  calc
    f z = f (∑ i, z i • (Pi.single i 1 : V → ℝ)) := congrArg f hz
    _ = ∑ i, f (Pi.single i 1) * z i := by
      simp [map_sum, map_smul, smul_eq_mul, mul_comm]

/-- All lower support inequalities characterize the finite convex hull. -/
theorem mem_hull_of_support_bounds (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (z : V → ℝ) (hs : ∀ p : V → ℝ, supportMin B p ≤ pairing p z) :
    z ∈ hull B := by
  by_contra hnot
  have hfinite : (toReal '' (B : Set (V → ℤ))).Finite :=
    (Finset.finite_toSet B).image toReal
  have hclosed : IsClosed (hull B) := hfinite.isClosed_convexHull ℝ
  have hconv : Convex ℝ (hull B) := convex_convexHull ℝ _
  obtain ⟨f,r,hfr,hrz⟩ := geometric_hahn_banach_closed_point hconv hclosed hnot
  let c : V → ℝ := fun i => -f (Pi.single i 1)
  have hc (y : V → ℝ) : pairing c y = -f y := by
    change (∑ i, (-f (Pi.single i 1)) * y i) = -f.toLinearMap y
    rw [linear_map_coordinates f.toLinearMap y]
    simp only [neg_mul, Finset.sum_neg_distrib, ContinuousLinearMap.coe_coe]
  have hlo : -r ≤ supportMin B c := by
    apply le_supportMin B hne c (-r)
    intro x hx
    have hxH : toReal x ∈ hull B := subset_convexHull ℝ _ ⟨x,hx,rfl⟩
    have hfx := hfr (toReal x) hxH
    rw [hc]
    exact neg_le_neg hfx.le
  have hp := hs c
  rw [hc] at hp
  linarith

lemma pairing_constant (t : ℝ) (x : V → ℤ) :
    pairing (fun _ => t) (toReal x) = t * (sumOn x Finset.univ : ℝ) := by
  simp [pairing, toReal, sumOn, Finset.mul_sum]

/-- C2 at a constant vector has only its terminal chain coefficient. -/
lemma c2_constant_value (h : (V → ℝ) → ℝ) (hc2 : SatisfiesC2 h) (t : ℝ) :
    h (fun _ => t) = t * h (charVec (Finset.univ : Finset V)) := by
  classical
  let σ : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  have hn : 0 < Fintype.card V := Fintype.card_pos
  let last : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have hlast : ¬ (last : ℕ) + 1 < Fintype.card V := by
    dsimp [last]
    omega
  have hprefix : Finset.univ.filter (fun v : V => σ.symm v ≤ last) = Finset.univ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have hv := (σ.symm v).isLt
    change (σ.symm v).val ≤ Fintype.card V - 1
    omega
  have hs := hc2 (fun _ => t) σ (fun _ _ _ => le_rfl)
  change h (fun _ => t) = ∑ j : Fin (Fintype.card V),
    (t - (if hj : (j : ℕ) + 1 < Fintype.card V then t else 0)) *
      h (charVec (Finset.univ.filter (fun v : V => σ.symm v ≤ j))) at hs
  rw [hs, Finset.sum_eq_single last]
  · simp only [dif_neg hlast, sub_zero, hprefix]
  · intro j hj hne
    have hjnext : (j : ℕ) + 1 < Fintype.card V := by
      by_contra h
      have hjlt := j.isLt
      have he : (j : ℕ) = Fintype.card V - 1 := by omega
      apply hne
      apply Fin.ext
      exact he
    simp only [dif_pos hjnext, sub_self, zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_univ last)).elim

/-- The negative constant test forces every member to have the minimum total. -/
lemma c2_common_total (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (hc2 : SatisfiesC2 (supportMin B)) (x : V → ℤ) (hx : x ∈ B) :
    sumOn x Finset.univ = B.inf' hne (fun y => sumOn y Finset.univ) := by
  have hconst := c2_constant_value (supportMin B) hc2 (-1)
  have h := supportMin_le_pairing B (fun _ => -1) hx
  rw [hconst, pairing_constant, supportMin_charVec B hne] at h
  have hreal : (sumOn x Finset.univ : ℝ) ≤
      ((B.inf' hne (fun y => sumOn y Finset.univ) : ℤ) : ℝ) := by linarith
  apply le_antisymm
  · exact_mod_cast hreal
  · exact B.inf'_le (fun y => sumOn y Finset.univ) hx

#print axioms mem_hull_of_support_bounds
#print axioms c2_constant_value
#print axioms c2_common_total
end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzLocalConverse.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SteinitzLocalRepair
open SteinitzExchange.LocalSupermod
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- With the required lattice saturation, C1 and C2 recover a supermodular base system. -/
theorem support_matroidal_implies_base (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (hconv : ∀ x : V → ℤ, toReal x ∈ hull B → x ∈ B)
    (hm : IsMatroidal (supportMin B)) : IsIntegralBaseSet B := by
  classical
  let g : Finset V → ℤ := fun X => B.inf' hne (fun x => sumOn x X)
  have hg0 : g ∅ = 0 := by simp [g, sumOn]
  have hg : IsSupermodular g := by
    intro X Y
    have h := hm.2.1 X Y
    change supportMin B (charVec X) + supportMin B (charVec Y) ≤
      supportMin B (charVec (X ∪ Y)) + supportMin B (charVec (X ∩ Y)) at h
    simp_rw [supportMin_charVec B hne] at h
    dsimp only [g]
    exact_mod_cast h
  have hlower (x : V → ℤ) (hx : x ∈ B) (X : Finset V) : g X ≤ sumOn x X :=
    B.inf'_le (fun y => sumOn y X) hx
  have htotal (x : V → ℤ) (hx : x ∈ B) : sumOn x Finset.univ = g Finset.univ :=
    c2_common_total B hne hm.2.2 x hx
  have hrep : ∀ x : V → ℤ, x ∈ B ↔
      (∀ X : Finset V, g X ≤ sumOn x X) ∧ sumOn x Finset.univ = g Finset.univ := by
    intro x
    constructor
    · intro hx
      exact ⟨hlower x hx, htotal x hx⟩
    · intro hx
      apply hconv x
      apply mem_hull_of_support_bounds B hne (toReal x)
      intro p
      obtain ⟨σ,hp⟩ := exists_antitone_indexing p
      have hc2 := hm.2.2 p σ hp
      change supportMin B p = ∑ j,
        chainCoefficient (p ∘ σ) j * supportMin B (charVec (chainPrefix σ j)) at hc2
      rw [hc2, pairing_chain_expansion σ p x]
      apply Finset.sum_le_sum
      intro j hj
      rw [supportMin_charVec B hne]
      change chainCoefficient (p ∘ σ) j * (g (chainPrefix σ j) : ℝ) ≤
        chainCoefficient (p ∘ σ) j * (sumOn x (chainPrefix σ j) : ℝ)
      by_cases hnext : (j : ℕ) + 1 < Fintype.card V
      · have hcoeff : 0 ≤ chainCoefficient (p ∘ σ) j := by
          rw [chainCoefficient, dif_pos hnext]
          exact sub_nonneg.mpr (hp (show j ≤ ⟨(j : ℕ) + 1,hnext⟩ from
            Fin.le_def.mpr (Nat.le_succ _)))
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hx.1 (chainPrefix σ j)) hcoeff
      · have he : (g (chainPrefix σ j) : ℝ) = (sumOn x (chainPrefix σ j) : ℝ) := by
          rw [chainPrefix_terminal σ j hnext, hx.2]
        exact le_of_eq (congrArg (fun t : ℝ => chainCoefficient (p ∘ σ) j * t) he)
  exact (SteinitzExchange.Duality.baseSet_iff_submodular_system B hne).2.1.mpr
    ⟨g,hg,hg0,hrep⟩

/-- The lattice-saturation premise is retained exactly in both directions. -/
theorem base_iff_support_matroidal_complete (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (hconv : ∀ x : V → ℤ, toReal x ∈ hull B → x ∈ B) :
    IsIntegralBaseSet B ↔ IsMatroidal (supportMin B) :=
  ⟨base_implies_support_matroidal B, support_matroidal_implies_base B hne hconv⟩

#print axioms support_matroidal_implies_base
#print axioms base_iff_support_matroidal_complete
end SteinitzLocalRepair
end

section
open SteinitzExchange.LocalSupermod

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (hconv : ∀ z : V → ℤ, toReal z ∈ hull B → z ∈ B) :
    IsIntegralBaseSet B ↔ IsMatroidal (supportMin B) :=
  SteinitzLocalRepair.base_iff_support_matroidal_complete B hne hconv

#print axioms solution
end
