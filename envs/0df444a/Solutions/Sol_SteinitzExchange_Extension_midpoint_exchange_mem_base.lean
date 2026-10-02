-- Prove2me | solution 1 for SteinitzExchange.Extension.midpoint_exchange_mem_base
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T17:52:37.673914+00:00
-- url     : https://prove2.me/submissions/1ed3252a-494e-46bc-97a3-77596a4bebec

import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Union
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp


open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem base_eq_of_coordinatewise_le {B : Finset (V → ℤ)}
    (hB : IsIntegralBaseSet B) {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (hxy : ∀ w, x w ≤ y w) : x = y := by
  ext u
  by_contra hne
  have hu : 0 < (y - x) u := by
    change 0 < y u - x u
    have := hxy u
    omega
  obtain ⟨v, hv, _⟩ := hB.2 y hy x hx u hu
  change y v - x v < 0 at hv
  have := hxy v
  omega

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

theorem sum_exchange (x : V → ℤ) (u v : V) :
    (∑ w, (x - chi u + chi v) w) = ∑ w, x w := by
  simp [Pi.add_apply, Pi.sub_apply, chi, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Pi.single_apply]

theorem base_sum_eq {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B) :
    (∑ w, x w) = ∑ w, y w := by
  classical
  let S := B.filter (fun z => (∑ w, z w) = ∑ w, x w)
  have hS : S.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image S (fun z => positiveDeviation z y) hS
  have hzB : z ∈ B := (Finset.mem_filter.mp hz).1
  have hzsum : (∑ w, z w) = ∑ w, x w := (Finset.mem_filter.mp hz).2
  have hzle : ∀ u, z u ≤ y u := by
    intro u
    by_contra hnot
    have hu : 0 < (z - y) u := by
      change 0 < z u - y u
      omega
    obtain ⟨v, hv, hz'⟩ := hB.2 z hzB y hy u hu
    have hmem : z - chi u + chi v ∈ S :=
      Finset.mem_filter.mpr ⟨hz', (sum_exchange z u v).trans hzsum⟩
    have hmin' := hmin _ hmem
    rw [positiveDeviation_exchange z y u v hu hv] at hmin'
    omega
  have hzy : z = y := base_eq_of_coordinatewise_le hB hzB hy hzle
  subst z
  exact hzsum.symm

#print axioms base_sum_eq

end SteinitzExchange.Extension

set_option autoImplicit false

open Set

namespace SteinitzCoordinator

/-- Symmetric basis exchange, extracted from the existing circuit-cocircuit API.
This is a local draft until its exact-environment compiler check succeeds. -/
theorem symmetric_basis_exchange {α : Type*} (M : Matroid α)
    {X Y : Set α} (hX : M.IsBase X) (hY : M.IsBase Y)
    {e : α} (he : e ∈ X \ Y) :
    ∃ f ∈ Y \ X,
      M.IsBase (insert f (X \ {e})) ∧ M.IsBase (insert e (Y \ {f})) := by
  have heE : e ∈ M.E := hX.subset_ground he.1
  have hC := hY.fundCircuit_isCircuit heE he.2
  have hK := hX.compl_closure_sdiff_singleton_isCocircuit he.1
  have heK : e ∈ M.E \ M.closure (X \ {e}) :=
    ⟨heE, hX.indep.notMem_closure_sdiff_of_mem he.1⟩
  have hn := hC.isCocircuit_inter_nontrivial hK
    ⟨e, M.mem_fundCircuit e Y, heK⟩
  obtain ⟨f, hf, hfe⟩ := hn.exists_ne e
  have hfY : f ∈ Y := by
    have h := M.fundCircuit_subset_insert e Y hf.1
    rcases h with h | h
    · exact (hfe h).elim
    · exact h
  have hfX : f ∉ X := by
    intro h
    exact hf.2.2 (M.subset_closure (X \ {e})
      (sdiff_subset.trans hX.subset_ground) ⟨h, hfe⟩)
  have hecl : e ∈ M.closure Y := by rwa [hY.closure_eq]
  have hi : M.Indep (insert e Y \ {f}) :=
    (hY.indep.mem_fundCircuit_iff hecl he.2).mp hf.1
  refine ⟨f, ⟨hfY, hfX⟩,
    hX.exchange_base_of_notMem_closure he.1 hf.2.2 hf.2.1, ?_⟩
  have hb := hY.exchange_isBase_of_indep' hfY he.2 hi
  simpa only [← insert_sdiff_singleton_comm hfe.symm] using hb

#print axioms symmetric_basis_exchange

end SteinitzCoordinator

open Set

namespace SteinitzCoordinator

variable {V : Type*} [DecidableEq V]

def cloneFiber (S : Set (V × ℕ)) (i : V) : Set ℕ :=
  {k | (i, k) ∈ S}

noncomputable def cloneCount (S : Set (V × ℕ)) (i : V) : ℤ :=
  (cloneFiber S i).ncard

lemma cloneFiber_finite {S : Set (V × ℕ)} (hS : S.Finite) (i : V) :
    (cloneFiber S i).Finite := by
  exact hS.preimage (fun _ _ _ _ h => (Prod.mk.inj h).2)

lemma cloneFiber_insert (S : Set (V × ℕ)) (u i : V) (k : ℕ) :
    cloneFiber (insert (u,k) S) i =
      if i = u then insert k (cloneFiber S i) else cloneFiber S i := by
  ext n
  by_cases h : i = u
  · subst i
    simp [cloneFiber]
  · simp [cloneFiber, h]

lemma cloneFiber_delete (S : Set (V × ℕ)) (u i : V) (k : ℕ) :
    cloneFiber (S \ {(u,k)}) i =
      if i = u then cloneFiber S i \ {k} else cloneFiber S i := by
  ext n
  by_cases h : i = u
  · subst i
    simp [cloneFiber]
  · simp [cloneFiber, h]

lemma cloneCount_insert {S : Set (V × ℕ)} (hS : S.Finite)
    (u : V) (k : ℕ) (hk : (u,k) ∉ S) (i : V) :
    cloneCount (insert (u,k) S) i = cloneCount S i + if i = u then 1 else 0 := by
  unfold cloneCount
  rw [cloneFiber_insert]
  split_ifs with h
  · subst i
    rw [Set.ncard_insert_of_notMem (show k ∉ cloneFiber S u from hk)
      (cloneFiber_finite hS u)]
    simp
  · simp

lemma cloneCount_delete {S : Set (V × ℕ)} (hS : S.Finite)
    (u : V) (k : ℕ) (hk : (u,k) ∈ S) (i : V) :
    cloneCount (S \ {(u,k)}) i = cloneCount S i - if i = u then 1 else 0 := by
  unfold cloneCount
  rw [cloneFiber_delete]
  split_ifs with h
  · subst i
    have hn := Set.ncard_sdiff_singleton_add_one
      (show k ∈ cloneFiber S u from hk) (cloneFiber_finite hS u)
    omega
  · simp

lemma cloneCount_mono {S T : Set (V × ℕ)} (hT : T.Finite)
    (hST : S ⊆ T) (i : V) : cloneCount S i ≤ cloneCount T i := by
  unfold cloneCount
  exact_mod_cast Set.ncard_le_ncard (s := cloneFiber S i) (t := cloneFiber T i)
    (fun k hk => hST hk) (cloneFiber_finite hT i)

lemma exists_clone_difference {S T : Set (V × ℕ)} (hS : S.Finite)
    (i : V) (h : cloneCount S i < cloneCount T i) :
    ∃ k, (i,k) ∈ T \ S := by
  by_contra hn
  have hsub : cloneFiber T i ⊆ cloneFiber S i := by
    intro k hk
    by_contra hkS
    exact hn ⟨k,hk,hkS⟩
  have hc := Set.ncard_le_ncard hsub (cloneFiber_finite hS i)
  unfold cloneCount at h
  omega

lemma exists_clone_same_coordinate {S T : Set (V × ℕ)} (hS : S.Finite)
    (u : V) (k : ℕ) (hk : (u,k) ∈ S \ T)
    (h : cloneCount S u ≤ cloneCount T u) :
    ∃ l, (u,l) ∈ T \ S := by
  by_contra hn
  have hsub : cloneFiber T u ⊆ cloneFiber S u \ {k} := by
    intro l hl
    refine ⟨?_, ?_⟩
    · by_contra hls
      exact hn ⟨l,hl,hls⟩
    · intro hlk
      have heq : l = k := Set.mem_singleton_iff.mp hlk
      change (u,l) ∈ T at hl
      rw [heq] at hl
      exact hk.2 hl
  have hc := Set.ncard_le_ncard hsub ((cloneFiber_finite hS u).sdiff)
  have hd := Set.ncard_sdiff_singleton_add_one
    (show k ∈ cloneFiber S u from hk.1) (cloneFiber_finite hS u)
  unfold cloneCount at h
  omega

lemma cloneCount_swap {S : Set (V × ℕ)} (hS : S.Finite)
    (u v : V) (k l : ℕ) (hk : (u,k) ∈ S) (hl : (v,l) ∉ S) (i : V) :
    cloneCount (insert (v,l) (S \ {(u,k)})) i =
      cloneCount S i - (if i = u then 1 else 0) + (if i = v then 1 else 0) := by
  rw [cloneCount_insert (hS.sdiff) v l (fun h => hl h.1) i,
    cloneCount_delete hS u k hk i]

variable [Fintype V]

def cloneLift (n : V → ℕ) : Finset (V × ℕ) :=
  Finset.univ.biUnion (fun i => (Finset.range (n i)).image (fun k => (i,k)))

@[simp] lemma mem_cloneLift (n : V → ℕ) (i : V) (k : ℕ) :
    (i,k) ∈ cloneLift n ↔ k < n i := by
  simp [cloneLift, Prod.mk.injEq]

lemma cloneFiber_lift (n : V → ℕ) (i : V) :
    cloneFiber (cloneLift n : Set (V × ℕ)) i = (Finset.range (n i) : Set ℕ) := by
  ext k
  simp [cloneFiber]

@[simp] lemma cloneCount_lift (n : V → ℕ) (i : V) :
    cloneCount (cloneLift n : Set (V × ℕ)) i = n i := by
  unfold cloneCount
  rw [cloneFiber_lift, Set.ncard_coe_finset, Finset.card_range]

end SteinitzCoordinator

open Set
open SteinitzExchange.Extension

namespace SteinitzCoordinator

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def shiftedCount (m : V → ℤ) (S : Set (V × ℕ)) : V → ℤ :=
  fun i => cloneCount S i + m i

noncomputable def cloneBase (m : V → ℤ) (B : Finset (V → ℤ))
    (S : Set (V × ℕ)) : Prop := S.Finite ∧ shiftedCount m S ∈ B

lemma shiftedCount_swap (m : V → ℤ) {S : Set (V × ℕ)} (hS : S.Finite)
    (u v : V) (k l : ℕ) (hk : (u,k) ∈ S) (hl : (v,l) ∉ S) :
    shiftedCount m (insert (v,l) (S \ {(u,k)})) =
      shiftedCount m S - chi u + chi v := by
  ext i
  simp only [shiftedCount, Pi.add_apply, Pi.sub_apply]
  rw [cloneCount_swap hS u v k l hk hl i]
  simp only [chi, Pi.single_apply]
  split_ifs <;> omega

lemma cloneBase_exchange (m : V → ℤ) {B : Finset (V → ℤ)}
    (hB : IsIntegralBaseSet B) : Matroid.ExchangeProperty (cloneBase m B) := by
  intro S T hS hT a ha
  rcases a with ⟨u,k⟩
  by_cases hle : cloneCount S u ≤ cloneCount T u
  · obtain ⟨l, hl⟩ := exists_clone_same_coordinate hS.1 u k ha hle
    refine ⟨(u,l), hl, (hS.1.sdiff).insert _, ?_⟩
    rw [shiftedCount_swap m hS.1 u u k l ha.1 hl.2]
    simpa using hS.2
  · have hu : 0 < (shiftedCount m S - shiftedCount m T) u := by
      simp only [shiftedCount, Pi.sub_apply]
      omega
    obtain ⟨v, hv, hb⟩ := hB.2 _ hS.2 _ hT.2 u hu
    have hlt : cloneCount S v < cloneCount T v := by
      simp only [shiftedCount, Pi.sub_apply] at hv
      omega
    obtain ⟨l, hl⟩ := exists_clone_difference hS.1 v hlt
    refine ⟨(v,l), hl, (hS.1.sdiff).insert _, ?_⟩
    rw [shiftedCount_swap m hS.1 u v k l ha.1 hl.2]
    exact hb

lemma shiftedCount_lift (m x : V → ℤ) (hx : ∀ i, m i ≤ x i) :
    shiftedCount m (cloneLift (fun i => (x i - m i).toNat) : Set (V × ℕ)) = x := by
  ext i
  simp only [shiftedCount, cloneCount_lift]
  have := hx i
  omega

/-- Symmetric exchange for an integral base set with an explicit coordinatewise lower bound.
No new axioms: finite integer vectors are expanded into finite bases on a countable clone ground. -/
theorem base_symmetric_exchange_with_lower_bound
    (m : V → ℤ) {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (hm : ∀ x ∈ B, ∀ i, m i ≤ x i)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (u : V) (hu : 0 < (x - y) u) :
    ∃ v : V, (x - y) v < 0 ∧
      x - chi u + chi v ∈ B ∧ y + chi u - chi v ∈ B := by
  classical
  let X : Set (V × ℕ) := cloneLift (fun i => (x i - m i).toNat)
  let Y : Set (V × ℕ) := cloneLift (fun i => (y i - m i).toNat)
  have hXfin : X.Finite := Finset.finite_toSet _
  have hYfin : Y.Finite := Finset.finite_toSet _
  have hXcount : shiftedCount m X = x := shiftedCount_lift m x (hm x hx)
  have hYcount : shiftedCount m Y = y := shiftedCount_lift m y (hm y hy)
  have hXB : cloneBase m B X := ⟨hXfin, hXcount.symm ▸ hx⟩
  have hYB : cloneBase m B Y := ⟨hYfin, hYcount.symm ▸ hy⟩
  let M : Matroid (V × ℕ) := Matroid.ofExistsFiniteIsBase Set.univ (cloneBase m B)
    ⟨X, hXB, hXfin⟩ (cloneBase_exchange m hB) (fun _ _ => Set.subset_univ _)
  have hXM : M.IsBase X := hXB
  have hYM : M.IsBase Y := hYB
  let k : ℕ := (y u - m u).toNat
  have hk : (u,k) ∈ X \ Y := by
    have hxu := hm x hx u
    have hyu := hm y hy u
    change 0 < x u - y u at hu
    simp only [X, Y, Set.mem_diff, Finset.mem_coe, mem_cloneLift, k]
    omega
  obtain ⟨⟨v,l⟩, hl, hbX, hbY⟩ := symmetric_basis_exchange M hXM hYM hk
  have hv : (x - y) v < 0 := by
    have hxv := hm x hx v
    have hyv := hm y hy v
    simp only [X, Y, Set.mem_diff, Finset.mem_coe, mem_cloneLift] at hl
    change x v - y v < 0
    omega
  change cloneBase m B (insert (v,l) (X \ {(u,k)})) at hbX
  change cloneBase m B (insert (u,k) (Y \ {(v,l)})) at hbY
  have hfirst := hbX.2
  have hsecond := hbY.2
  rw [shiftedCount_swap m hXfin u v k l hk.1 hl.2, hXcount] at hfirst
  rw [shiftedCount_swap m hYfin v u l k hl.1 hk.2, hYcount] at hsecond
  refine ⟨v,hv,hfirst,?_⟩
  convert hsecond using 1 <;> abel

theorem base_symmetric_exchange {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (u : V) (hu : 0 < (x - y) u) :
    ∃ v : V, (x - y) v < 0 ∧
      x - chi u + chi v ∈ B ∧ y + chi u - chi v ∈ B := by
  classical
  let m : V → ℤ := fun i => B.inf' hB.1 (fun z => z i)
  apply base_symmetric_exchange_with_lower_bound m hB _ hx hy u hu
  intro z hz i
  exact Finset.inf'_le (fun a => a i) hz

#print axioms base_symmetric_exchange

end SteinitzCoordinator


open scoped BigOperators

namespace SteinitzExchange.Extension

section Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def transferWeights (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ) : ι → ℝ :=
  fun i => w i - (if i = a then ε else 0) - (if i = b then ε else 0) +
    (if i = a' then ε else 0) + (if i = b' then ε else 0)

theorem transferWeights_nonneg (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hab : a ≠ b) (he : 0 ≤ ε)
    (hea : ε ≤ w a) (heb : ε ≤ w b) :
    ∀ i, 0 ≤ transferWeights w a b a' b' ε i := by
  intro i
  have hp : 0 ≤ (if i = a' then ε else 0) := by split_ifs <;> first | exact he | exact le_rfl
  have hq : 0 ≤ (if i = b' then ε else 0) := by split_ifs <;> first | exact he | exact le_rfl
  unfold transferWeights
  by_cases hia : i = a
  · subst i
    simp only [if_neg hab, ite_true]
    linarith
  · by_cases hib : i = b
    · subst i
      simp only [if_neg hia, ite_true]
      linarith
    · simp only [if_neg hia, if_neg hib]
      have := hw i
      linarith

theorem sum_transferWeights (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ) :
    (∑ i, transferWeights w a b a' b' ε i) = ∑ i, w i := by
  simp only [transferWeights, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp <;> ring

theorem weighted_sum_transfer {E : Type*} [AddCommGroup E] [Module ℝ E]
    (w : ι → ℝ) (p : ι → E) (a b a' b' : ι) (ε : ℝ) :
    (∑ i, transferWeights w a b a' b' ε i • p i) =
      (∑ i, w i • p i) - ε • p a - ε • p b + ε • p a' + ε • p b' := by
  simp [transferWeights, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ite_smul]

theorem transferWeights_mem_stdSimplex (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ)
    (hw : w ∈ stdSimplex ℝ ι) (hab : a ≠ b) (he : 0 ≤ ε)
    (hea : ε ≤ w a) (heb : ε ≤ w b) :
    transferWeights w a b a' b' ε ∈ stdSimplex ℝ ι :=
  ⟨transferWeights_nonneg w a b a' b' ε hw.1 hab he hea heb,
    (sum_transferWeights w a b a' b' ε).trans hw.2⟩

theorem barycenter_transfer_eq {E : Type*} [AddCommGroup E] [Module ℝ E]
    (w : ι → ℝ) (p : ι → E) (a b a' b' : ι) (ε : ℝ)
    (hp : p a' + p b' = p a + p b) :
    (∑ i, transferWeights w a b a' b' ε i • p i) = ∑ i, w i • p i := by
  rw [weighted_sum_transfer]
  have heq := congrArg (fun z => ε • z) hp
  simp only [smul_add] at heq
  calc
    _ = (∑ i, w i • p i) - (ε • p a + ε • p b) +
        (ε • p a' + ε • p b') := by abel
    _ = _ := by rw [heq]; exact sub_add_cancel _ _

end Weights

section Energy

variable {V : Type*} [Fintype V] [DecidableEq V]

def integerEnergy (x : V → ℤ) : ℤ := ∑ w, (x w) ^ 2

theorem integerEnergy_exchange (a b : V → ℤ) (u v : V) (huv : u ≠ v) :
    integerEnergy (a - chi u + chi v) + integerEnergy (b + chi u - chi v) -
      integerEnergy a - integerEnergy b =
        -2 * (a u - b u) + 2 * (a v - b v) + 4 := by
  have hpoint : ∀ w,
      ((a - chi u + chi v) w) ^ 2 + ((b + chi u - chi v) w) ^ 2 -
          (a w) ^ 2 - (b w) ^ 2 =
        (if w = u then -2 * (a u - b u) + 2 else 0) +
        (if w = v then 2 * (a v - b v) + 2 else 0) := by
    intro w
    by_cases hwu : w = u
    · subst w
      simp [chi, Pi.single_apply, huv] <;> ring
    · by_cases hwv : w = v
      · subst w
        simp [chi, Pi.single_apply, hwu] <;> ring
      · simp [chi, Pi.single_apply, hwu, hwv]
  unfold integerEnergy
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp <;> ring

theorem integerEnergy_exchange_lt (a b : V → ℤ) (u v : V)
    (hu : b u + 2 ≤ a u) (hv : a v < b v) :
    integerEnergy (a - chi u + chi v) + integerEnergy (b + chi u - chi v) <
      integerEnergy a + integerEnergy b := by
  have huv : u ≠ v := by intro h; subst v; omega
  have he := integerEnergy_exchange a b u v huv
  omega

end Energy

end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

section ConvexWeights

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]

theorem convexHull_range_exists_weights (p : ι → E) {c : E}
    (hc : c ∈ convexHull ℝ (Set.range p)) :
    ∃ w : ι → ℝ, w ∈ stdSimplex ℝ ι ∧ ∑ i, w i • p i = c := by
  have hconv : Convex ℝ {z : E | ∃ w : ι → ℝ,
      w ∈ stdSimplex ℝ ι ∧ ∑ i, w i • p i = z} := by
    rintro x ⟨w, hw, rfl⟩ y ⟨v, hv, rfl⟩ a b ha hb hab
    refine ⟨a • w + b • v, (convex_stdSimplex ℝ ι) hw hv ha hb hab, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, ← Finset.smul_sum]
  apply convexHull_min ?_ hconv hc
  rintro _ ⟨i, rfl⟩
  refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
  simp [Pi.single_apply, ite_smul]

end ConvexWeights

section BaseWeights

variable {V : Type*} [Fintype V] [DecidableEq V]

def baseBarycenter (A : Finset (V → ℤ)) (w : A → ℝ) : V → ℝ :=
  ∑ a : A, w a • toReal a.1

def weightedEnergy (A : Finset (V → ℤ)) (w : A → ℝ) : ℝ :=
  ∑ a : A, w a * (integerEnergy a.1 : ℝ)

theorem hull_exists_weights (A : Finset (V → ℤ)) {c : V → ℝ}
    (hc : c ∈ hull A) :
    ∃ w : A → ℝ, w ∈ stdSimplex ℝ A ∧ baseBarycenter A w = c := by
  have hr : Set.range (fun a : A => toReal a.1) =
      toReal '' (A : Set (V → ℤ)) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  apply convexHull_range_exists_weights (fun a : A => toReal a.1)
  simpa only [hr, hull] using hc

theorem hull_coordinate_sum_eq (A : Finset (V → ℤ)) (hA : IsIntegralBaseSet A)
    (a : V → ℤ) (ha : a ∈ A) {c : V → ℝ} (hc : c ∈ hull A) :
    (∑ v, c v) = ((∑ v, a v : ℤ) : ℝ) := by
  obtain ⟨w, hw, hbar⟩ := hull_exists_weights A hc
  rw [← hbar]
  simp only [baseBarycenter, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toReal]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← Int.cast_sum]
  have hs : ∀ b : A, (∑ v, b.1 v) = ∑ v, a v :=
    fun b => base_sum_eq hA b.2 ha
  simp_rw [hs]
  rw [← Finset.sum_mul, hw.2, one_mul]

theorem exists_minimal_energy_weights (A : Finset (V → ℤ)) {c : V → ℝ}
    (hc : c ∈ hull A) :
    ∃ w : A → ℝ, w ∈ stdSimplex ℝ A ∧ baseBarycenter A w = c ∧
      ∀ v : A → ℝ, v ∈ stdSimplex ℝ A → baseBarycenter A v = c →
        weightedEnergy A w ≤ weightedEnergy A v := by
  let K : Set (A → ℝ) := stdSimplex ℝ A ∩ {w | baseBarycenter A w = c}
  have hbar : Continuous (baseBarycenter A) := by unfold baseBarycenter; fun_prop
  have henergy : Continuous (weightedEnergy A) := by unfold weightedEnergy; fun_prop
  have hcompact : IsCompact K :=
    (isCompact_stdSimplex ℝ A).inter_right (isClosed_eq hbar continuous_const)
  obtain ⟨w, hw, hbarw⟩ := hull_exists_weights A hc
  obtain ⟨v, hv, hmin⟩ := hcompact.exists_isMinOn ⟨w, hw, hbarw⟩ henergy.continuousOn
  exact ⟨v, hv.1, hv.2, fun z hz hbarz => hmin ⟨hz, hbarz⟩⟩

def SymmetricBaseExchange (A : Finset (V → ℤ)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ u : V, b u < a u →
    ∃ v : V, a v < b v ∧ a - chi u + chi v ∈ A ∧ b + chi u - chi v ∈ A

theorem minimal_energy_support_close (A : Finset (V → ℤ))
    (hA : SymmetricBaseExchange A) {c : V → ℝ} (w : A → ℝ)
    (hw : w ∈ stdSimplex ℝ A) (hbar : baseBarycenter A w = c)
    (hmin : ∀ v : A → ℝ, v ∈ stdSimplex ℝ A → baseBarycenter A v = c →
      weightedEnergy A w ≤ weightedEnergy A v) :
    ∀ a b : A, 0 < w a → 0 < w b → ∀ u, a.1 u ≤ b.1 u + 1 := by
  classical
  intro a b ha hb u
  by_contra hnot
  have hu : b.1 u + 2 ≤ a.1 u := by omega
  obtain ⟨v, hv, ha', hb'⟩ := hA a.1 a.2 b.1 b.2 u (by omega)
  let a' : A := ⟨a.1 - chi u + chi v, ha'⟩
  let b' : A := ⟨b.1 + chi u - chi v, hb'⟩
  let ε := min (w a) (w b)
  have he : 0 < ε := lt_min ha hb
  have hab : a ≠ b := by intro h; subst b; omega
  let w' := transferWeights w a b a' b' ε
  have hw' : w' ∈ stdSimplex ℝ A :=
    transferWeights_mem_stdSimplex w a b a' b' ε hw hab (le_of_lt he)
      (min_le_left _ _) (min_le_right _ _)
  have hp : toReal a'.1 + toReal b'.1 = toReal a.1 + toReal b.1 := by
    ext z
    simp [a', b', toReal] <;> ring
  have hbar' : baseBarycenter A w' = c := by
    change (∑ i : A, transferWeights w a b a' b' ε i • toReal i.1) = c
    rw [barycenter_transfer_eq w (fun i : A => toReal i.1) a b a' b' ε hp]
    exact hbar
  have henergy : (integerEnergy a'.1 : ℝ) + integerEnergy b'.1 <
      integerEnergy a.1 + integerEnergy b.1 := by
    exact_mod_cast integerEnergy_exchange_lt a.1 b.1 u v hu hv
  have hdrop := mul_lt_mul_of_pos_left henergy he
  have htransfer : weightedEnergy A w' = weightedEnergy A w -
      ε * integerEnergy a.1 - ε * integerEnergy b.1 +
      ε * integerEnergy a'.1 + ε * integerEnergy b'.1 := by
    simpa only [weightedEnergy, w', smul_eq_mul] using
      weighted_sum_transfer w (fun i : A => (integerEnergy i.1 : ℝ)) a b a' b' ε
  have hcontr := hmin w' hw' hbar'
  rw [htransfer] at hcontr
  nlinarith

theorem balanced_support_mem_integer_box (A : Finset (V → ℤ))
    {c : V → ℝ} (w : A → ℝ) (hw : w ∈ stdSimplex ℝ A)
    (hbar : baseBarycenter A w = c)
    (hclose : ∀ a b : A, 0 < w a → 0 < w b → ∀ u, a.1 u ≤ b.1 u + 1)
    (lo hi : V → ℤ) (hlo : ∀ u, (lo u : ℝ) ≤ c u)
    (hhi : ∀ u, c u ≤ (hi u : ℝ)) :
    ∀ a : A, 0 < w a → ∀ u, lo u ≤ a.1 u ∧ a.1 u ≤ hi u := by
  classical
  intro a ha u
  have hcoord : (∑ b : A, w b * (b.1 u : ℝ)) = c u := by
    simpa [baseBarycenter, toReal, Finset.sum_apply] using congrFun hbar u
  constructor
  · by_contra hnot
    have hal : a.1 u < lo u := by omega
    have hle : ∀ b : A, w b * (b.1 u : ℝ) ≤ w b * (lo u : ℝ) := by
      intro b
      by_cases hb : 0 < w b
      · have hbi : b.1 u ≤ lo u := by have := hclose b a hb ha u; omega
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbi) (hw.1 b)
      · have hb0 : w b = 0 := le_antisymm (le_of_not_gt hb) (hw.1 b)
        simp [hb0]
    have hlt : (∑ b : A, w b * (b.1 u : ℝ)) < ∑ b : A, w b * (lo u : ℝ) :=
      Finset.sum_lt_sum (fun b _ => hle b)
        ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left (by exact_mod_cast hal) ha⟩
    rw [hcoord, ← Finset.sum_mul, hw.2, one_mul] at hlt
    exact (not_lt_of_ge (hlo u)) hlt
  · by_contra hnot
    have hai : hi u < a.1 u := by omega
    have hle : ∀ b : A, w b * (hi u : ℝ) ≤ w b * (b.1 u : ℝ) := by
      intro b
      by_cases hb : 0 < w b
      · have hbi : hi u ≤ b.1 u := by have := hclose a b ha hb u; omega
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbi) (hw.1 b)
      · have hb0 : w b = 0 := le_antisymm (le_of_not_gt hb) (hw.1 b)
        simp [hb0]
    have hlt : (∑ b : A, w b * (hi u : ℝ)) < ∑ b : A, w b * (b.1 u : ℝ) :=
      Finset.sum_lt_sum (fun b _ => hle b)
        ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left (by exact_mod_cast hai) ha⟩
    rw [hcoord, ← Finset.sum_mul, hw.2, one_mul] at hlt
    exact (not_lt_of_ge (hhi u)) hlt

theorem symmetricBaseExchange_hull_box (A : Finset (V → ℤ))
    (hA : SymmetricBaseExchange A) {c : V → ℝ} (hc : c ∈ hull A)
    (lo hi : V → ℤ) (hlo : ∀ u, (lo u : ℝ) ≤ c u)
    (hhi : ∀ u, c u ≤ (hi u : ℝ)) :
    c ∈ hull (A.filter (fun a => ∀ u, lo u ≤ a u ∧ a u ≤ hi u)) := by
  classical
  obtain ⟨w, hw, hbar, hmin⟩ := exists_minimal_energy_weights A hc
  have hclose := minimal_energy_support_close A hA w hw hbar hmin
  have hbox := balanced_support_mem_integer_box A w hw hbar hclose lo hi hlo hhi
  let t := Finset.univ.filter (fun a : A => 0 < w a)
  have hout : ∀ a : A, a ∉ t → w a = 0 := by
    intro a hnot
    have hnonpos : w a ≤ 0 := le_of_not_gt (by simpa [t] using hnot)
    exact le_antisymm hnonpos (hw.1 a)
  have hsum : ∑ a ∈ t, w a = 1 := by
    rw [← hw.2]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ hnot
    exact hout a hnot
  have hbar' : ∑ a ∈ t, w a • toReal a.1 = c := by
    rw [← hbar]
    unfold baseBarycenter
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ hnot
    simp [hout a hnot]
  have hmem : t.centerMass w (fun a : A => toReal a.1) ∈
      convexHull ℝ (toReal '' (A.filter (fun a => ∀ u, lo u ≤ a u ∧ a u ≤ hi u) :
        Set (V → ℤ))) := by
    apply t.centerMass_mem_convexHull (fun a _ => hw.1 a) (by rw [hsum]; norm_num)
    intro a ha
    exact ⟨a.1, Finset.mem_filter.mpr ⟨a.2, hbox a (by simpa [t] using ha)⟩, rfl⟩
  rw [Finset.centerMass_eq_of_sum_1 _ _ hsum, hbar'] at hmem
  exact hmem

#print axioms symmetricBaseExchange_hull_box

end BaseWeights

end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

theorem binary_complement_of_overlap_zero (r a b : V → ℤ)
    (hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1)
    (ha : ∀ v, 0 ≤ a v ∧ a v ≤ r v)
    (hb : ∀ v, 0 ≤ b v ∧ b v ≤ r v)
    (hsum : (∑ v, a v) + (∑ v, b v) = ∑ v, r v)
    (hoverlap : (∑ v, a v * b v) = 0) :
    ∀ v, a v + b v = r v := by
  have hprod : ∀ v, a v * b v = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => mul_nonneg (ha v).1 (hb v).1)).mp hoverlap
    exact fun v => h v (Finset.mem_univ v)
  have hle : ∀ v, a v + b v ≤ r v := by
    intro v
    rcases mul_eq_zero.mp (hprod v) with h | h <;>
      have := ha v <;> have := hb v <;> omega
  have heq : (∑ v, (a v + b v)) = ∑ v, r v := by
    rw [Finset.sum_add_distrib]
    exact hsum
  have h := (Finset.sum_eq_sum_iff_of_le (fun v _ => hle v)).mp heq
  exact fun v => h v (Finset.mem_univ v)

/-- Rank at most two: half marginals force complementary support vectors. -/
theorem binary_half_marginals_complement (r : V → ℤ) (p : ι → V → ℤ)
    (k : ℤ) (hk : k ≤ 2)
    (hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1)
    (hp : ∀ i v, 0 ≤ p i v ∧ p i v ≤ r v)
    (hsum : ∀ i, (∑ v, p i v) = k)
    (hrsum : (∑ v, r v) = 2 * k)
    (w : ι → ℝ) (hw : w ∈ stdSimplex ℝ ι)
    (hmean : ∀ v, (∑ i, w i * (p i v : ℝ)) = (r v : ℝ) / 2) :
    ∃ a b : ι, 0 < w a ∧ 0 < w b ∧ ∀ v, p a v + p b v = r v := by
  classical
  have haex : ∃ a, 0 < w a := by
    by_contra h
    push_neg at h
    have hnonpos : (∑ i, w i) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    rw [hw.2] at hnonpos
    norm_num at hnonpos
  obtain ⟨a, ha⟩ := haex
  let overlap : ι → ℤ := fun b => ∑ v, p a v * p b v
  have hoverlap_nonneg : ∀ b, 0 ≤ overlap b :=
    fun b => Finset.sum_nonneg (fun v _ => mul_nonneg (hp a v).1 (hp b v).1)
  have har : ∀ v, p a v * r v = p a v := by
    intro v
    have hrv := hr v
    have hav := hp a v
    have hcases : r v = 0 ∨ r v = 1 := by omega
    rcases hcases with h | h
    · have hpa : p a v = 0 := by omega
      simp [hpa]
    · simp [h]
  have hself : overlap a = k := by
    change (∑ v, p a v * p a v) = k
    rw [← hsum a]
    apply Finset.sum_congr rfl
    intro v _
    have hrv := hr v
    have hav := hp a v
    have hcases : p a v = 0 ∨ p a v = 1 := by omega
    rcases hcases with h | h <;> simp [h]
  have hmean_overlap : (∑ b, w b * (overlap b : ℝ)) = (k : ℝ) / 2 := by
    calc
      _ = ∑ v, (p a v : ℝ) * (∑ b, w b * (p b v : ℝ)) := by
        simp only [overlap, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ∑ v, (p a v : ℝ) * ((r v : ℝ) / 2) := by simp_rw [hmean]
      _ = (∑ v, (p a v : ℝ)) / 2 := by
        simp_rw [← mul_div_assoc, ← Int.cast_mul, har]
        simp only [div_eq_mul_inv, Finset.sum_mul]
      _ = (k : ℝ) / 2 := by rw [← Int.cast_sum, hsum a]
  have hbex : ∃ b, 0 < w b ∧ overlap b = 0 := by
    by_contra h
    push_neg at h
    have hle : ∀ b, w b ≤ w b * (overlap b : ℝ) := by
      intro b
      by_cases hb : 0 < w b
      · have hbi : (1 : ℤ) ≤ overlap b := by
          have := hoverlap_nonneg b
          have := h b hb
          omega
        have hbr : (1 : ℝ) ≤ overlap b := by exact_mod_cast hbi
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hbr (hw.1 b)
      · have hb0 : w b = 0 := le_antisymm (le_of_not_gt hb) (hw.1 b)
        simp [hb0]
    have hsum_le := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hle b)
    rw [hw.2, hmean_overlap] at hsum_le
    have hkreal : (2 : ℝ) ≤ k := by linarith
    have hkint : (2 : ℤ) ≤ k := by exact_mod_cast hkreal
    have hk2 : k = 2 := le_antisymm hk hkint
    have hlt : (∑ b, w b) < ∑ b, w b * (overlap b : ℝ) := by
      apply Finset.sum_lt_sum (fun b _ => hle b)
      refine ⟨a, Finset.mem_univ a, ?_⟩
      rw [hself, hk2]
      norm_num
      linarith
    rw [hw.2, hmean_overlap, hk2] at hlt
    norm_num at hlt
  obtain ⟨b, hb, hab⟩ := hbex
  refine ⟨a, b, ha, hb, binary_complement_of_overlap_zero r (p a) (p b)
    hr (hp a) (hp b) ?_ hab⟩
  rw [hsum a, hsum b, hrsum]
  omega

#print axioms binary_half_marginals_complement

end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem integralBase_symmetric (A : Finset (V → ℤ)) (hA : IsIntegralBaseSet A) :
    SymmetricBaseExchange A := by
  intro a ha b hb u hu
  obtain ⟨v, hv, hav, hbv⟩ := SteinitzCoordinator.base_symmetric_exchange hA ha hb u
    (by simpa only [Pi.sub_apply, sub_pos] using hu)
  exact ⟨v, by simpa only [Pi.sub_apply, sub_neg] using hv, hav, hbv⟩

theorem toReal_mem_hull_iff_checked (A : Finset (V → ℤ))
    (hA : IsIntegralBaseSet A) (x : V → ℤ) : toReal x ∈ hull A ↔ x ∈ A := by
  classical
  constructor
  · intro hx
    have hb := symmetricBaseExchange_hull_box A (integralBase_symmetric A hA) hx x x
      (fun _ => le_rfl) (fun _ => le_rfl)
    have hn : (toReal '' (A.filter (fun a => ∀ u, x u ≤ a u ∧ a u ≤ x u) :
        Set (V → ℤ))).Nonempty := (convexHull_nonempty_iff).mp ⟨toReal x, hb⟩
    rcases hn with ⟨z, a, ha, _⟩
    obtain ⟨haA, hax⟩ := Finset.mem_filter.mp ha
    have he : a = x := funext (fun u => le_antisymm (hax u).2 (hax u).1)
    exact he ▸ haA
  · intro hx
    exact subset_convexHull ℝ _ ⟨x, hx, rfl⟩

#print axioms toReal_mem_hull_iff_checked

/-- The substantial convex-geometric core: a midpoint at lattice distance four
has a complementary pair in the integral base set containing that midpoint. -/
theorem base_midpoint_complement (A : Finset (V → ℤ)) (hA : IsIntegralBaseSet A)
    (x y : V → ℤ) (hxySum : (∑ v, x v) = ∑ v, y v)
    (hxy : (∑ v, |x v - y v|) = 4)
    (hm : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull A) :
    ∃ a ∈ A, ∃ b ∈ A, a + b = x + y ∧
      ∀ v, min (x v) (y v) ≤ a v ∧ a v ≤ max (x v) (y v) := by
  classical
  let c : V → ℝ := (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y
  let lo : V → ℤ := fun v => (x v + y v) / 2
  let hi : V → ℤ := fun v => x v + y v - lo v
  let r : V → ℤ := fun v => x v + y v - 2 * lo v
  let k : ℤ := (∑ v, x v) - ∑ v, lo v
  have hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1 := by
    intro v
    dsimp [r, lo]
    omega
  have hlo : ∀ v, (lo v : ℝ) ≤ c v := by
    intro v
    have hdiv : 2 * lo v ≤ x v + y v := by dsimp [lo]; omega
    have hdivR : 2 * (lo v : ℝ) ≤ (x v : ℝ) + y v := by exact_mod_cast hdiv
    dsimp [c, toReal]
    linarith
  have hhi : ∀ v, c v ≤ (hi v : ℝ) := by
    intro v
    have hdiv : x v + y v ≤ 2 * hi v := by dsimp [hi, lo]; omega
    have hdivR : (x v : ℝ) + y v ≤ 2 * (hi v : ℝ) := by exact_mod_cast hdiv
    dsimp [c, toReal]
    linarith
  have hsumc : (∑ v, c v) = ((∑ v, x v : ℤ) : ℝ) := by
    simp only [c, Pi.add_apply, Pi.smul_apply, toReal, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Int.cast_sum, ← hxySum]
    ring
  have hsumA : ∀ a : A, (∑ v, a.1 v) = ∑ v, x v := by
    intro a
    have he := (hull_coordinate_sum_eq A hA a.1 a.2 hm).symm.trans hsumc
    exact_mod_cast he
  have hrsum : (∑ v, r v) = 2 * k := by
    simp only [r, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← hxySum, k]
    ring
  have hrle : ∀ v, r v ≤ |x v - y v| := by
    intro v
    by_cases he : x v = y v
    · dsimp [r, lo]
      rw [he]
      simp only [sub_self, abs_zero]
      omega
    · have habs : 0 < |x v - y v| := abs_pos.mpr (sub_ne_zero.mpr he)
      have := hr v
      omega
  have hk : k ≤ 2 := by
    have h := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hrle v)
    rw [hrsum, hxy] at h
    omega
  obtain ⟨w, hw, hbar, hmin⟩ := exists_minimal_energy_weights A hm
  have hclose := minimal_energy_support_close A (integralBase_symmetric A hA) w hw hbar hmin
  have hbox := balanced_support_mem_integer_box A w hw hbar hclose lo hi hlo hhi
  let t := Finset.univ.filter (fun a : A => 0 < w a)
  have hpos : ∀ a : t, 0 < w a.1 := by intro a; simpa [t] using a.2
  have hout : ∀ a : A, a ∉ t → w a = 0 := by
    intro a hnot
    exact le_antisymm (le_of_not_gt (by simpa [t] using hnot)) (hw.1 a)
  have hsumt : ∑ a ∈ t, w a = 1 := by
    rw [← hw.2]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ hnot
    exact hout a hnot
  let wt : t → ℝ := fun a => w a.1
  let p : t → V → ℤ := fun a v => a.1.1 v - lo v
  have hwt : wt ∈ stdSimplex ℝ t :=
    ⟨fun a => hw.1 a.1, by simpa only [wt, Finset.sum_coe_sort] using hsumt⟩
  have hp : ∀ a v, 0 ≤ p a v ∧ p a v ≤ r v := by
    intro a v
    have h := hbox a.1 (hpos a) v
    dsimp [p, hi, r] at *
    omega
  have hpsum : ∀ a, (∑ v, p a v) = k := by
    intro a
    simp only [p, Finset.sum_sub_distrib, hsumA, k]
  have hmean : ∀ v, (∑ a, wt a * (p a v : ℝ)) = (r v : ℝ) / 2 := by
    intro v
    have hcoord : (∑ a : A, w a * (a.1 v : ℝ)) = c v := by
      simpa [baseBarycenter, toReal, Finset.sum_apply, c] using congrFun hbar v
    have hcoordt : (∑ a ∈ t, w a * (a.1 v : ℝ)) = c v := by
      rw [← hcoord]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ hnot
      simp [hout a hnot]
    have hcoordt' : (∑ a : t, wt a * (a.1.1 v : ℝ)) = c v := by
      change (∑ a : t, w a.1 * (a.1.1 v : ℝ)) = c v
      exact (Finset.sum_coe_sort t (fun a : A => w a * (a.1 v : ℝ))).trans hcoordt
    calc
      _ = (∑ a : t, wt a * (a.1.1 v : ℝ)) - (∑ a : t, wt a) * (lo v : ℝ) := by
        simp [p, Int.cast_sub, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      _ = c v - (lo v : ℝ) := by rw [hcoordt', hwt.2, one_mul]
      _ = (r v : ℝ) / 2 := by simp [c, r, toReal]; ring
  obtain ⟨a, b, ha, hb, hab⟩ :=
    binary_half_marginals_complement r p k hk hr hp hpsum hrsum wt hwt hmean
  refine ⟨a.1.1, a.1.2, b.1.1, b.1.2, ?_, ?_⟩
  · ext v
    have h := hab v
    dsimp [p, r] at h
    change a.1.1 v + b.1.1 v = x v + y v
    omega
  · intro v
    have h := hbox a.1 (hpos a) v
    have hlow : min (x v) (y v) ≤ lo v := by dsimp [lo]; omega
    have hhigh : hi v ≤ max (x v) (y v) := by dsimp [hi, lo]; omega
    exact ⟨hlow.trans h.1, h.2.trans hhigh⟩

#print axioms base_midpoint_complement

end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem int_nonneg_sum_one_single (p : V → ℤ) (hp : ∀ v, 0 ≤ p v)
    (hs : (∑ v, p v) = 1) : ∃ u, ∀ v, p v = if v = u then 1 else 0 := by
  classical
  have hex : ∃ u, 0 < p u := by
    by_contra h
    push_neg at h
    have hz : ∀ v, p v = 0 := fun v => le_antisymm (h v) (hp v)
    simp [hz] at hs
  obtain ⟨u, hu⟩ := hex
  have hle : p u ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun v _ => hp v) (Finset.mem_univ u)
  have hpu : p u = 1 := by omega
  have herase : (∑ v ∈ Finset.univ.erase u, p v) = 0 := by
    have h := Finset.sum_erase_add Finset.univ p (Finset.mem_univ u)
    rw [hs, hpu] at h
    omega
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun v (_ : v ∈ Finset.univ.erase u) => hp v)).mp herase
  refine ⟨u, fun v => ?_⟩
  by_cases hv : v = u
  · subst v
    simp [hpu]
  · simp [hv, hz v (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩)]

theorem l1_eq_twice_positiveDeviation (x y : V → ℤ)
    (hs : (∑ v, x v) = ∑ v, y v) :
    (∑ v, |x v - y v|) = 2 * positiveDeviation x y := by
  have hpoint : ∀ v, |x v - y v| = 2 * max (x v - y v) 0 - (x v - y v) := by
    intro v
    by_cases h : 0 ≤ x v - y v
    · rw [abs_of_nonneg h, max_eq_left h]
      omega
    · have h' : x v - y v ≤ 0 := le_of_lt (lt_of_not_ge h)
      rw [abs_of_nonpos h', max_eq_right h']
      omega
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hs,
    sub_self, sub_zero]
  rfl

theorem l1_pos_of_ne (x y : V → ℤ) (hne : x ≠ y) : 0 < ∑ v, |x v - y v| := by
  have hex : ∃ v, x v ≠ y v := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨v, hv⟩ := hex
  have hpos : 0 < |x v - y v| := abs_pos.mpr (sub_ne_zero.mpr hv)
  exact lt_of_lt_of_le hpos
    (Finset.single_le_sum (fun w _ => abs_nonneg (x w - y w)) (Finset.mem_univ v))

theorem l1_two_unit_exchange (x a : V → ℤ)
    (hs : (∑ v, x v) = ∑ v, a v) (hd : (∑ v, |x v - a v|) = 2) :
    ∃ u v, 0 < (x - a) u ∧ (x - a) v < 0 ∧ a = x - chi u + chi v := by
  have hp : positiveDeviation x a = 1 := by
    have h := l1_eq_twice_positiveDeviation x a hs
    omega
  have hq : positiveDeviation a x = 1 := by
    have h := l1_eq_twice_positiveDeviation a x hs.symm
    have hd' : (∑ v, |a v - x v|) = 2 := by simpa only [abs_sub_comm] using hd
    omega
  obtain ⟨u, hu⟩ := int_nonneg_sum_one_single (fun v => max (x v - a v) 0)
    (fun _ => le_max_right _ _) hp
  obtain ⟨v, hv⟩ := int_nonneg_sum_one_single (fun v => max (a v - x v) 0)
    (fun _ => le_max_right _ _) hq
  have hup : 0 < (x - a) u := by
    have h := hu u
    simp only [ite_true] at h
    change 0 < x u - a u
    omega
  have hvn : (x - a) v < 0 := by
    have h := hv v
    simp only [ite_true] at h
    change x v - a v < 0
    omega
  refine ⟨u, v, hup, hvn, ?_⟩
  ext z
  have hpz := hu z
  have hqz := hv z
  simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply]
  omega

theorem l1_add_of_between (x a y : V → ℤ)
    (hbox : ∀ v, min (x v) (y v) ≤ a v ∧ a v ≤ max (x v) (y v)) :
    (∑ v, |x v - a v|) + (∑ v, |a v - y v|) = ∑ v, |x v - y v| := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have h := hbox v
  by_cases hxy : x v ≤ y v
  · have hxa : x v ≤ a v := by simpa [min_eq_left hxy] using h.1
    have hay : a v ≤ y v := by simpa [max_eq_right hxy] using h.2
    rw [abs_of_nonpos (sub_nonpos.mpr hxa), abs_of_nonpos (sub_nonpos.mpr hay),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    omega
  · have hyx : y v ≤ x v := le_of_lt (lt_of_not_ge hxy)
    have hya : y v ≤ a v := by simpa [min_eq_right hyx] using h.1
    have hax : a v ≤ x v := by simpa [max_eq_left hyx] using h.2
    rw [abs_of_nonneg (sub_nonneg.mpr hax), abs_of_nonneg (sub_nonneg.mpr hya),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    omega

theorem midpoint_exchange_mem_base_checked [Nonempty V]
    (B A : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (hA : IsIntegralBaseSet A)
    (x y : V → ℤ) (hx : x ∈ B) (hy : y ∈ B) (hxy : ∑ w, |x w - y w| = 4)
    (hm : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull A) :
    ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧
      x - chi u + chi v ∈ A ∧ y + chi u - chi v ∈ A := by
  classical
  have hsum := base_sum_eq hB hx hy
  have hne : x ≠ y := by intro h; subst y; simp at hxy
  have hpositive : ∃ u, 0 < (x - y) u := by
    by_contra h
    push_neg at h
    have hle : ∀ u, x u ≤ y u := by
      intro u
      have h' := h u
      change x u - y u ≤ 0 at h'
      omega
    exact hne (base_eq_of_coordinatewise_le hB hx hy hle)
  have hdirect (hxA : x ∈ A) (hyA : y ∈ A) :
      ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧
        x - chi u + chi v ∈ A ∧ y + chi u - chi v ∈ A := by
    obtain ⟨u, hu⟩ := hpositive
    obtain ⟨v, hv, hxv, hyv⟩ :=
      SteinitzCoordinator.base_symmetric_exchange hA hxA hyA u hu
    exact ⟨u, v, hu, hv, hxv, hyv⟩
  obtain ⟨a, ha, b, hb, hab, hbox⟩ := base_midpoint_complement A hA x y hsum hxy hm
  by_cases hax : a = x
  · subst a
    have hby : b = y := add_left_cancel hab
    exact hdirect ha (hby ▸ hb)
  by_cases hay : a = y
  · subst a
    have hbx : b = x := by
      calc
        b = (y + b) - y := by abel
        _ = (x + y) - y := by rw [hab]
        _ = x := by abel
    exact hdirect (hbx ▸ hb) ha
  have hsa : (∑ v, a v) = ∑ v, x v := by
    have hca := hull_coordinate_sum_eq A hA a ha hm
    have hsumc : (∑ v, ((1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y) v) =
        ((∑ v, x v : ℤ) : ℝ) := by
      simp only [Pi.add_apply, Pi.smul_apply, toReal, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Int.cast_sum, ← hsum]
      ring
    exact_mod_cast hca.symm.trans hsumc
  have hdistadd := l1_add_of_between x a y hbox
  have hpos1 := l1_pos_of_ne x a (Ne.symm hax)
  have hpos2 := l1_pos_of_ne a y hay
  have hpar1 := l1_eq_twice_positiveDeviation x a hsa.symm
  have hpar2 := l1_eq_twice_positiveDeviation a y (hsa.trans hsum)
  have hdist : (∑ v, |x v - a v|) = 2 := by omega
  obtain ⟨u, v, hu, hv, haexpr⟩ := l1_two_unit_exchange x a hsa.symm hdist
  have huy : 0 < (x - y) u := by
    have h := hbox u
    change 0 < x u - a u at hu
    change 0 < x u - y u
    omega
  have hvy : (x - y) v < 0 := by
    have h := hbox v
    change x v - a v < 0 at hv
    change x v - y v < 0
    omega
  have hbexpr : b = y + chi u - chi v := by
    apply add_left_cancel (a := x - chi u + chi v)
    calc
      _ = x + y := by simpa only [haexpr] using hab
      _ = _ := by abel
  exact ⟨u, v, huy, hvy, haexpr ▸ ha, hbexpr ▸ hb⟩

#print axioms midpoint_exchange_mem_base_checked

end SteinitzExchange.Extension

open SteinitzExchange.Extension

-- Mission: Convexity and Steinitz's Exchange Property I, Extension Theorem
-- Target: https://prove2.me/theorems/3ac8d0ff-c3a8-4428-b097-3c19f40868c2
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B A : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (hA : IsIntegralBaseSet A)
    (x y : V → ℤ) (hx : x ∈ B) (hy : y ∈ B) (hxy : ∑ w, |x w - y w| = 4)
    (hm : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull A) :
    ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧
      x - chi u + chi v ∈ A ∧ y + chi u - chi v ∈ A :=
  midpoint_exchange_mem_base_checked B A hB hA x y hx hy hxy hm

#print axioms solution
