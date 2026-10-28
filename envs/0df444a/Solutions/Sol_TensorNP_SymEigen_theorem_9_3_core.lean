-- Prove2me | solution 1 for TensorNP.SymEigen.theorem_9_3_core
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T04:54:40.807104+00:00
-- url     : https://prove2.me/submissions/f29be0f8-51e8-43de-9926-c3293e3d98ff

import Mathlib
import Definitions.Def_TensorNP_SymEigen_StabTensor
import Definitions.Def_TensorNP_SymEigen_Defs

/-
Apache-2.0. Independent proof of the complete native unit tensor eigenvalue characterization.
Credit: shivm established the mission support for symmetry/cubic form; no accepted proof source was copied.
The proof below establishes genuine support-merging, literal tensor contractions, the unit cubic bound, and an explicit normalized attained eigenvector. This is not a formal TM-hardness claim.
-/

-- BEGIN TSEProof.MultisetEntries
section

namespace TensorNP.SymEigen.TSEFresh
open Classical

theorem pair_multiset_eq {ι : Type*} (a b c d : ι) :
    ({a,b} : Multiset ι) = {c,d} ↔ (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  simp only [Multiset.insert_eq_cons, ←Multiset.cons_zero]
  constructor
  · intro h
    have ha : a=c ∨ a=d := by
      have hm : a ∈ a ::ₘ b ::ₘ (0 : Multiset ι) := by simp
      rw [h] at hm
      simpa using hm
    rcases ha with ha | ha
    · subst a
      left; exact ⟨rfl, by simpa using h⟩
    · subst a
      rw [Multiset.cons_swap c d] at h
      right; exact ⟨rfl, by simpa using h⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact Multiset.cons_swap _ _ _

theorem triple_multiset_eq {ι : Type*} (a b c x y z : ι) :
    ({a,b,c} : Multiset ι) = {x,y,z} ↔
      (a=x ∧ ((b=y ∧ c=z) ∨ (b=z ∧ c=y))) ∨
      (a=y ∧ ((b=x ∧ c=z) ∨ (b=z ∧ c=x))) ∨
      (a=z ∧ ((b=x ∧ c=y) ∨ (b=y ∧ c=x))) := by
  simp only [Multiset.insert_eq_cons, ←Multiset.cons_zero]
  constructor
  · intro h
    have ha : a=x ∨ a=y ∨ a=z := by
      have hm : a ∈ a ::ₘ b ::ₘ c ::ₘ (0 : Multiset ι) := by simp
      rw [h] at hm
      simpa using hm
    rcases ha with ha | ha | ha
    · subst a
      exact Or.inl ⟨rfl, (pair_multiset_eq _ _ _ _).mp (by simpa using h)⟩
    · subst a
      rw [Multiset.cons_swap x y] at h
      exact Or.inr (Or.inl ⟨rfl, (pair_multiset_eq _ _ _ _).mp (by simpa using h)⟩)
    · subst a
      rw [Multiset.cons_swap y z, Multiset.cons_swap x z] at h
      exact Or.inr (Or.inr ⟨rfl, (pair_multiset_eq _ _ _ _).mp (by simpa using h)⟩)
  · rintro (⟨ha,h⟩ | ⟨ha,h⟩ | ⟨ha,h⟩)
    · rw [ha]
      exact congrArg (Multiset.cons x) ((pair_multiset_eq _ _ _ _).mpr h)
    · rw [ha, Multiset.cons_swap x y]
      exact congrArg (Multiset.cons y) ((pair_multiset_eq _ _ _ _).mpr h)
    · rw [ha, Multiset.cons_swap y z, Multiset.cons_swap x z]
      exact congrArg (Multiset.cons z) ((pair_multiset_eq _ _ _ _).mpr h)

end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.MultisetEntries

-- BEGIN TSEProof.TensorEntries
section
namespace TensorNP.SymEigen.TSEFresh
open Classical
noncomputable section
variable {v : ℕ}

theorem tensor_vvp (G : SimpleGraph (Fin v)) (i j : Fin v) (p : PairIdx v) :
    stabTensor G (.inl i) (.inl j) (.inr p) =
      if ¬ G.Adj p.1.1 p.1.2 ∧
        ((i=p.1.1 ∧ j=p.1.2) ∨ (i=p.1.2 ∧ j=p.1.1)) then 1 else 0 := by
  unfold stabTensor
  congr 1
  simp only [triple_multiset_eq, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, or_false]
  aesop

theorem tensor_swap_last (G : SimpleGraph (Fin v)) (a b c : Idx v) :
    stabTensor G a b c = stabTensor G a c b := by
  have h : ({a,b,c} : Multiset (Idx v)) = {a,c,b} := by
    change a ::ₘ b ::ₘ c ::ₘ 0 = a ::ₘ c ::ₘ b ::ₘ 0
    rw [Multiset.cons_swap b c]
  simp only [stabTensor, h]

theorem tensor_swap_first (G : SimpleGraph (Fin v)) (a b c : Idx v) :
    stabTensor G a b c = stabTensor G b a c := by
  have h : ({a,b,c} : Multiset (Idx v)) = {b,a,c} := by
    exact Multiset.cons_swap _ _ _
  simp only [stabTensor, h]

@[simp] theorem tensor_vvv (G : SimpleGraph (Fin v)) (i j k : Fin v) :
    stabTensor G (.inl i) (.inl j) (.inl k) = 0 := by
  simp only [stabTensor, triple_multiset_eq]
  simp

@[simp] theorem tensor_vpp (G : SimpleGraph (Fin v)) (i : Fin v) (p q : PairIdx v) :
    stabTensor G (.inl i) (.inr p) (.inr q) = 0 := by
  simp only [stabTensor, triple_multiset_eq]
  simp

@[simp] theorem tensor_ppp (G : SimpleGraph (Fin v)) (p q r : PairIdx v) :
    stabTensor G (.inr p) (.inr q) (.inr r) = 0 := by
  simp only [stabTensor, triple_multiset_eq]
  simp

end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.TensorEntries

-- BEGIN TSEProof.TensorContraction
section
namespace TensorNP.SymEigen.TSEFresh
open Classical
open scoped BigOperators
noncomputable section
variable {v : ℕ}

theorem tensor_vvp_split (G : SimpleGraph (Fin v)) (i j : Fin v) (p : PairIdx v) :
    stabTensor G (.inl i) (.inl j) (.inr p) =
      if ¬G.Adj p.1.1 p.1.2 then
        (if i=p.1.1 then if j=p.1.2 then 1 else 0 else 0) +
        (if i=p.1.2 then if j=p.1.1 then 1 else 0 else 0) else 0 := by
  have hp : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  rw [tensor_vvp]
  split_ifs <;> simp_all

theorem contraction_pair (G : SimpleGraph (Fin v)) (z : Idx v → ℝ) (p : PairIdx v) :
    (∑ i, ∑ j, stabTensor G i j (.inr p) * z i * z j) =
      if ¬G.Adj p.1.1 p.1.2 then 2*z (.inl p.1.1)*z (.inl p.1.2) else 0 := by
  simp only [Fintype.sum_sum_type]
  have hpv (q : PairIdx v) (i : Fin v) :
      stabTensor G (.inr q) (.inl i) (.inr p) = 0 := by
    rw [tensor_swap_first, tensor_vpp]
  simp only [tensor_vpp, tensor_ppp, hpv, zero_mul, Finset.sum_const_zero, add_zero]
  simp only [tensor_vvp_split]
  by_cases h : ¬G.Adj p.1.1 p.1.2
  · simp [h, add_mul, ite_mul, Finset.sum_add_distrib]
    ring
  · simp [h]

theorem contraction_vertex (G : SimpleGraph (Fin v)) (z : Idx v → ℝ) (i : Fin v) :
    (∑ a, ∑ b, stabTensor G a b (.inl i) * z a * z b) =
      2 * ∑ p : PairIdx v, if ¬G.Adj p.1.1 p.1.2 then
        ((if i=p.1.1 then z (.inl p.1.2) else 0) +
         (if i=p.1.2 then z (.inl p.1.1) else 0))*z (.inr p) else 0 := by
  have hvp (j : Fin v) (p : PairIdx v) :
      stabTensor G (.inl j) (.inr p) (.inl i) =
        stabTensor G (.inl i) (.inl j) (.inr p) := by
    rw [tensor_swap_last, tensor_swap_first]
  have hpv (p : PairIdx v) (j : Fin v) :
      stabTensor G (.inr p) (.inl j) (.inl i) =
        stabTensor G (.inl i) (.inl j) (.inr p) := by
    rw [tensor_swap_first, hvp]
  have hpp (p q : PairIdx v) : stabTensor G (.inr p) (.inr q) (.inl i) = 0 := by
    rw [tensor_swap_last, tensor_swap_first, tensor_vpp]
  simp only [Fintype.sum_sum_type, tensor_vvv, hpp, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero, hvp, hpv]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [tensor_vvp_split]
  by_cases h : ¬G.Adj p.1.1 p.1.2
  · simp [h, add_mul, mul_add, ite_mul, mul_ite, Finset.sum_add_distrib]
    split_ifs <;> ring
  · simp [h]
end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.TensorContraction

-- BEGIN TSEProof.PairSums
section
namespace TensorNP.SymEigen.TSEFresh
open Classical
open scoped BigOperators
noncomputable section
variable {v : ℕ}

theorem sum_pairs (f : Fin v → Fin v → ℝ) :
    (∑ p : PairIdx v, f p.1.1 p.1.2) = ∑ i, ∑ j, if i<j then f i j else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin v × Fin v => p.1 < p.2))
    (by simp) (fun p => f p.1 p.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem sum_pairs_both (f : Fin v → Fin v → ℝ) :
    (∑ p : PairIdx v, (f p.1.1 p.1.2 + f p.1.2 p.1.1)) =
      ∑ i, ∑ j, if i≠j then f i j else 0 := by
  rw [Finset.sum_add_distrib, sum_pairs f, sum_pairs (fun i j => f j i)]
  conv_lhs => rhs; rw [Finset.sum_comm]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt_of_ge h.le, ne_of_lt h]
  · simp
  · simp [h, not_lt_of_ge h.le, (ne_of_lt h).symm]
end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.PairSums

-- BEGIN TSEProof.PairIncidence
section
namespace TensorNP.SymEigen.TSEFresh
open Classical
open scoped BigOperators
noncomputable section
variable {v : ℕ}

theorem pair_incidence_sum (f : Fin v → ℝ) (i : Fin v) :
    (∑ p : PairIdx v, ((if i=p.1.1 then f p.1.2 else 0) +
      (if i=p.1.2 then f p.1.1 else 0))) = ∑ j, if j≠i then f j else 0 := by
  have h := sum_pairs_both (fun a b => if a=i then f b else 0)
  have he (a b : Fin v) :
      (if a≠b then if a=i then f b else 0 else 0) =
      if a=i then if b≠i then f b else 0 else 0 := by
    split_ifs <;> simp_all
  simp_rw [he] at h
  simpa [eq_comm] using h

theorem pair_product_sum (u : Fin v → ℝ) :
    2 * (∑ p : PairIdx v, u p.1.1*u p.1.2) =
      (∑ i, u i)^2 - ∑ i, u i^2 := by
  have h := sum_pairs_both (fun i j => u i*u j)
  have he (i j : Fin v) :
      (if i≠j then u i*u j else 0) = u i*u j - (if i=j then u i^2 else 0) := by
    split_ifs <;> simp_all [sq]
  simp_rw [he, Finset.sum_sub_distrib] at h
  simp only [←Finset.mul_sum, ←Finset.sum_mul] at h
  have hl : (∑ p : PairIdx v, (u p.1.1*u p.1.2+u p.1.2*u p.1.1)) =
      2*(∑ p : PairIdx v, u p.1.1*u p.1.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hl] at h
  simpa [sq] using h
end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.PairIncidence

-- BEGIN TSEProof.IndependentVector
section
namespace TensorNP.SymEigen.TSEFresh
open Classical
open scoped BigOperators
noncomputable section
variable {v : ℕ}

def independentVector (S : Finset (Fin v)) (a b : ℝ) : Idx v → ℝ :=
  Sum.elim (fun i => if i∈S then a else 0)
    (fun p => if p.1.1∈S ∧ p.1.2∈S then b else 0)

theorem independentVector_square_sum (S : Finset (Fin v)) (a b : ℝ) :
    (∑ k, independentVector S a b k ^2) =
      (S.card:ℝ)*a^2 + ((S.card:ℝ)^2-S.card)/2*b^2 := by
  have hp := pair_product_sum (fun i => if i∈S then (1:ℝ) else 0)
  have he (i j : Fin v) : (if i∈S then (1:ℝ) else 0)*(if j∈S then (1:ℝ) else 0) =
      if i∈S ∧ j∈S then (1:ℝ) else 0 := by
    split_ifs <;> simp_all
  simp_rw [he] at hp
  simp only [ite_pow] at hp
  simp at hp
  have hc : (∑ p : PairIdx v, if p.1.1∈S ∧ p.1.2∈S then (1:ℝ) else 0) =
      ((S.card:ℝ)^2-S.card)/2 := by
    simp
    linarith
  simp only [Fintype.sum_sum_type, independentVector, Sum.elim_inl, Sum.elim_inr,
    ite_pow, zero_pow (by decide : 2 ≠ 0)]
  have hb : (∑ p : PairIdx v, if p.1.1∈S ∧ p.1.2∈S then b^2 else 0) =
      (∑ p : PairIdx v, if p.1.1∈S ∧ p.1.2∈S then (1:ℝ) else 0)*b^2 := by
    rw [Finset.sum_mul]
    simp only [ite_mul, one_mul, zero_mul]
  rw [hb,hc]
  simp

theorem independentVector_pair (G : SimpleGraph (Fin v)) (S : Finset (Fin v))
    (hS : G.IsIndepSet (S : Set (Fin v))) (a b : ℝ) (p : PairIdx v) :
    (∑ i, ∑ j, stabTensor G i j (.inr p) * independentVector S a b i *
      independentVector S a b j) =
      if p.1.1∈S ∧ p.1.2∈S then 2*a^2 else 0 := by
  rw [contraction_pair]
  simp only [independentVector, Sum.elim_inl]
  have hi := G.isIndepSet_iff.mp hS
  by_cases h : p.1.1∈S ∧ p.1.2∈S
  · have hn := hi h.1 h.2 (ne_of_lt p.2)
    simp [h, hn, sq, mul_assoc]
  · rcases not_and_or.mp h with h1 | h2
    · simp [h1]
    · simp [h2]

theorem independentVector_vertex (G : SimpleGraph (Fin v)) (S : Finset (Fin v))
    (hS : G.IsIndepSet (S : Set (Fin v))) (a b : ℝ) (i : Fin v) :
    (∑ j, ∑ k, stabTensor G j k (.inl i) * independentVector S a b j *
      independentVector S a b k) =
      if i∈S then 2*((S.card:ℝ)-1)*a*b else 0 := by
  rw [contraction_vertex]
  simp only [independentVector, Sum.elim_inl, Sum.elim_inr]
  have hi := G.isIndepSet_iff.mp hS
  have he (p : PairIdx v) :
      (if ¬G.Adj p.1.1 p.1.2 then
        ((if i=p.1.1 then if p.1.2∈S then a else 0 else 0) +
         (if i=p.1.2 then if p.1.1∈S then a else 0 else 0))*
        (if p.1.1∈S ∧ p.1.2∈S then b else 0) else 0) =
      if i∈S then a*b*((if i=p.1.1 then if p.1.2∈S then (1:ℝ) else 0 else 0)+
        (if i=p.1.2 then if p.1.1∈S then (1:ℝ) else 0 else 0)) else 0 := by
    have hn : p.1.1∈S → p.1.2∈S → ¬G.Adj p.1.1 p.1.2 :=
      fun h1 h2 => hi h1 h2 (ne_of_lt p.2)
    split_ifs <;> simp_all
    ring
  simp_rw [he]
  by_cases h : i∈S
  · simp only [h, if_true, ←Finset.mul_sum]
    rw [pair_incidence_sum (fun j => if j∈S then (1:ℝ) else 0) i]
    have hs : (∑ j : Fin v, if j≠i then if j∈S then (1:ℝ) else 0 else 0) =
        (S.card:ℝ)-1 := by
      have hh : (∑ j : Fin v, if j≠i then if j∈S then (1:ℝ) else 0 else 0) =
          ∑ j ∈ S.erase i, (1:ℝ) := by
        simp only [←Finset.sum_filter]
        congr 1
        ext j
        simp
      rw [hh]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem h]
      rw [Nat.cast_sub (Finset.one_le_card.mpr ⟨i,h⟩)]
      norm_num
    rw [hs]
    ring
  · simp [h]
end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.IndependentVector

-- BEGIN TSEProof.LambdaComparison
section

namespace TensorNP.SymEigen.TSEFresh

 theorem lambdaL_sq {l : ℕ} (hl : 1 ≤ l) :
    (lambdaL l) ^ 2 = (8 / 3 : ℝ) * (1 - 1 / (l : ℝ)) := by
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlp : (0 : ℝ) < l := lt_of_lt_of_le (by norm_num) hlr
  have hdiv : (1 : ℝ) / l ≤ 1 := (div_le_one hlp).mpr hlr
  have hn : 0 ≤ (2 / 3 : ℝ) * (1 - 1 / (l : ℝ)) := by positivity
  unfold lambdaL
  rw [mul_pow, Real.sq_sqrt hn]
  ring

 theorem lambda_index_le {l a : ℕ} (hl : 1 ≤ l) (ha : 1 ≤ a)
    (h : (lambdaL l) ^ 2 ≤ (8 / 3 : ℝ) * (1 - 1 / (a : ℝ))) : l ≤ a := by
  have hlp : (0 : ℝ) < l := by exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 1) hl)
  have hap : (0 : ℝ) < a := by exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 1) ha)
  rw [lambdaL_sq hl] at h
  have hrec : (1 : ℝ) / a ≤ 1 / l := by linarith
  have hle := (div_le_div_iff₀ hap hlp).mp hrec
  simp only [one_mul] at hle
  exact_mod_cast hle

end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.LambdaComparison

-- BEGIN TSEProof.AttainmentScalars
section
namespace TensorNP.SymEigen.TSEFresh

theorem attainment_scalars {m : ℕ} (hm : 2 ≤ m) :
    ∃ a b : ℝ,
      (m:ℝ)*a^2+((m:ℝ)^2-m)/2*b^2=1 ∧
      2*((m:ℝ)-1)*a*b=lambdaL m*a ∧ 2*a^2=lambdaL m*b := by
  have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m:ℝ) ≠ 0 := by linarith
  have hm1 : (m:ℝ)-1 ≠ 0 := by linarith
  let a : ℝ := Real.sqrt (2/(3*(m:ℝ)))
  let b : ℝ := lambdaL m/(2*((m:ℝ)-1))
  have ha : a^2=2/(3*(m:ℝ)) := Real.sq_sqrt (by positivity)
  have hl := lambdaL_sq (show 1 ≤ m by omega)
  have hb : b^2 = (2/(3*(m:ℝ)))/((m:ℝ)-1) := by
    dsimp [b]
    rw [div_pow, hl]
    field_simp
    ring
  refine ⟨a,b,?_,?_,?_⟩
  · rw [ha,hb]
    field_simp
    ring
  · dsimp [b]
    field_simp
  · rw [ha]
    dsimp [b]
    have he : lambdaL m * (lambdaL m / (2*((m:ℝ)-1))) =
        (lambdaL m)^2 / (2*((m:ℝ)-1)) := by ring
    rw [he, hl]
    field_simp
    ring
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.AttainmentScalars

-- BEGIN TSEProof.Attainment
section
namespace TensorNP.SymEigen.TSEFresh
open Classical
open scoped BigOperators
noncomputable section
variable {v : ℕ}

theorem independent_set_eigenvalue (G : SimpleGraph (Fin v)) (S : Finset (Fin v))
    (hS : G.IsIndepSet (S : Set (Fin v))) (hcard : 2 ≤ S.card) :
    IsUnitL2Eigenvalue (stabTensor G) (lambdaL S.card) := by
  obtain ⟨a,b,hn,hv,hp⟩ := attainment_scalars hcard
  refine ⟨independentVector S a b, ?_, ?_⟩
  · unfold l2norm
    rw [independentVector_square_sum, hn]
    exact Real.sqrt_one
  · intro k
    rcases k with i | p
    · rw [independentVector_vertex G S hS]
      simp only [independentVector, Sum.elim_inl]
      by_cases h : i∈S
      · simpa [h] using hv
      · simp [h]
    · rw [independentVector_pair G S hS]
      simp only [independentVector, Sum.elim_inr]
      by_cases h : p.1.1∈S ∧ p.1.2∈S
      · simpa [h] using hp
      · simp [h]

theorem zero_eigenvalue (hv : 0<v) (G : SimpleGraph (Fin v)) :
    IsUnitL2Eigenvalue (stabTensor G) (lambdaL 1) := by
  let i : Fin v := ⟨0,hv⟩
  let z : Idx v → ℝ := fun k => if k=Sum.inl i then 1 else 0
  refine ⟨z,?_,?_⟩
  · simp [l2norm, z]
  · intro k
    simp only [z, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have hz : stabTensor G (.inl i) (.inl i) k=0 := by
      rcases k with j | p
      · exact tensor_vvv G i i j
      · rw [tensor_vvp]
        have hp := ne_of_lt p.2
        split_ifs with h
        · rcases h.2 with h | h
          · exact (hp (h.1.symm.trans h.2)).elim
          · exact (hp (h.2.symm.trans h.1)).elim
        · rfl
    rw [hz]
    simp [lambdaL]
end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.Attainment

-- BEGIN TSEProof.NonedgeForm
section

namespace TensorNP.SymEigen.TSEFresh

noncomputable section
open scoped BigOperators
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

 def nonedgeCoeff (G : SimpleGraph V) (i j : V) : ℝ :=
  if i ≠ j ∧ ¬ G.Adj i j then 1 else 0

def nonedgeBilin (G : SimpleGraph V) (p q : V → ℝ) : ℝ :=
  ∑ i, ∑ j, nonedgeCoeff G i j * p i * q j

def nonedgeDegree (G : SimpleGraph V) (p : V → ℝ) (i : V) : ℝ :=
  ∑ j, nonedgeCoeff G i j * p j

def orderedNonedgeSum (G : SimpleGraph V) (p : V → ℝ) : ℝ :=
  nonedgeBilin G p p

omit [Fintype V] in
 theorem nonedgeCoeff_symm (G : SimpleGraph V) (i j : V) :
    nonedgeCoeff G i j = nonedgeCoeff G j i := by
  classical
  simp only [nonedgeCoeff, ne_comm, G.adj_comm]

omit [Fintype V] in
@[simp] theorem nonedgeCoeff_self (G : SimpleGraph V) (i : V) :
    nonedgeCoeff G i i = 0 := by
  simp [nonedgeCoeff]

omit [Fintype V] in
 theorem nonedgeCoeff_of_adj (G : SimpleGraph V) {i j : V} (h : G.Adj i j) :
    nonedgeCoeff G i j = 0 := by
  simp [nonedgeCoeff, h]

theorem nonedgeBilin_comm (G : SimpleGraph V) (p q : V → ℝ) :
    nonedgeBilin G p q = nonedgeBilin G q p := by
  unfold nonedgeBilin
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [nonedgeCoeff_symm]
  ring

theorem nonedgeBilin_add_left (G : SimpleGraph V) (p q z : V → ℝ) :
    nonedgeBilin G (p + q) z = nonedgeBilin G p z + nonedgeBilin G q z := by
  simp [nonedgeBilin, mul_add, add_mul, Finset.sum_add_distrib]

theorem nonedgeBilin_sub_left (G : SimpleGraph V) (p q z : V → ℝ) :
    nonedgeBilin G (p - q) z = nonedgeBilin G p z - nonedgeBilin G q z := by
  simp [nonedgeBilin, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem nonedgeBilin_add_right (G : SimpleGraph V) (p q z : V → ℝ) :
    nonedgeBilin G p (q + z) = nonedgeBilin G p q + nonedgeBilin G p z := by
  rw [nonedgeBilin_comm, nonedgeBilin_add_left]
  rw [nonedgeBilin_comm G q p, nonedgeBilin_comm G z p]

theorem nonedgeBilin_sub_right (G : SimpleGraph V) (p q z : V → ℝ) :
    nonedgeBilin G p (q - z) = nonedgeBilin G p q - nonedgeBilin G p z := by
  rw [nonedgeBilin_comm, nonedgeBilin_sub_left]
  rw [nonedgeBilin_comm G q p, nonedgeBilin_comm G z p]

theorem nonedgeBilin_single_left (G : SimpleGraph V) (i : V) (a : ℝ) (p : V → ℝ) :
    nonedgeBilin G (Pi.single i a) p = a * nonedgeDegree G p i := by
  classical
  unfold nonedgeBilin
  rw [Finset.sum_comm]
  simp only [Pi.single_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [nonedgeDegree, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem nonedgeBilin_single_right (G : SimpleGraph V) (i : V) (a : ℝ) (p : V → ℝ) :
    nonedgeBilin G p (Pi.single i a) = a * nonedgeDegree G p i := by
  rw [nonedgeBilin_comm, nonedgeBilin_single_left]

theorem nonedgeDegree_single (G : SimpleGraph V) (i j : V) (a : ℝ) :
    nonedgeDegree G (Pi.single j a) i = nonedgeCoeff G i j * a := by
  classical
  simp [nonedgeDegree, Pi.single_apply, mul_ite]

theorem orderedNonedgeSum_eq (G : SimpleGraph V) (p : V → ℝ) :
    orderedNonedgeSum G p =
      ∑ i, ∑ j, if i ≠ j ∧ ¬ G.Adj i j then p i * p j else 0 := by
  classical
  simp [orderedNonedgeSum, nonedgeBilin, nonedgeCoeff, ite_mul]

end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.NonedgeForm

-- BEGIN TSEProof.MassTransfer
section

namespace TensorNP.SymEigen.TSEFresh

noncomputable section
open scoped BigOperators
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def massMove (p : V → ℝ) (i j : V) : V → ℝ :=
  p + Pi.single i (p j) - Pi.single j (p j)

def massSupport (p : V → ℝ) : Finset V :=
  Finset.univ.filter (fun i => p i ≠ 0)

omit [DecidableEq V] in
@[simp] theorem mem_massSupport (p : V → ℝ) (i : V) :
    i ∈ massSupport p ↔ p i ≠ 0 := by
  simp [massSupport]

omit [Fintype V] in
 theorem massMove_apply (p : V → ℝ) {i j : V} (hij : i ≠ j) (k : V) :
    massMove p i j k = if k = i then p i + p j else if k = j then 0 else p k := by
  by_cases hki : k = i
  · subst k
    simp [massMove, hij]
  · by_cases hkj : k = j
    · subst k
      simp [massMove, hki]
    · simp [massMove, hki, hkj]

 theorem massMove_sum (p : V → ℝ) (i j : V) :
    ∑ k, massMove p i j k = ∑ k, p k := by
  simp [massMove, Pi.single_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]

omit [Fintype V] in
 theorem massMove_nonneg (p : V → ℝ) (hp : ∀ k, 0 ≤ p k) {i j : V}
    (hij : i ≠ j) : ∀ k, 0 ≤ massMove p i j k := by
  intro k
  rw [massMove_apply p hij]
  split_ifs
  · exact add_nonneg (hp i) (hp j)
  · exact le_rfl
  · exact hp k

 theorem massMove_support_subset (p : V → ℝ) {i j : V} (hij : i ≠ j)
    (hi : p i ≠ 0) : massSupport (massMove p i j) ⊆ (massSupport p).erase j := by
  intro k hk
  simp only [Finset.mem_erase, mem_massSupport] at hk ⊢
  rw [massMove_apply p hij] at hk
  constructor
  · intro hkj
    subst k
    simp [Ne.symm hij] at hk
  · by_cases hki : k = i
    · simpa [hki] using hi
    · by_cases hkj : k = j
      · subst k
        simp [Ne.symm hij] at hk
      · simpa [hki, hkj] using hk

 theorem massMove_support_card_lt (p : V → ℝ) {i j : V} (hij : i ≠ j)
    (hi : p i ≠ 0) (hj : p j ≠ 0) :
    (massSupport (massMove p i j)).card < (massSupport p).card := by
  exact lt_of_le_of_lt (Finset.card_le_card (massMove_support_subset p hij hi))
    (Finset.card_erase_lt_of_mem (by simpa using hj))

 theorem orderedNonedgeSum_massMove (G : SimpleGraph V) (p : V → ℝ)
    {i j : V} (hij : G.Adj i j) :
    orderedNonedgeSum G (massMove p i j) = orderedNonedgeSum G p +
      2 * p j * (nonedgeDegree G p i - nonedgeDegree G p j) := by
  unfold massMove orderedNonedgeSum
  simp only [nonedgeBilin_sub_left, nonedgeBilin_add_left]
  simp only [nonedgeBilin_sub_right, nonedgeBilin_add_right]
  simp only [nonedgeBilin_single_left, nonedgeBilin_single_right, nonedgeDegree_single,
    nonedgeCoeff_self, nonedgeCoeff_of_adj G hij, nonedgeCoeff_of_adj G hij.symm,
    zero_mul, mul_zero]
  ring

 theorem orderedNonedgeSum_massMove_le (G : SimpleGraph V) (p : V → ℝ)
    (hp : ∀ k, 0 ≤ p k) {i j : V} (hij : G.Adj i j)
    (hdeg : nonedgeDegree G p j ≤ nonedgeDegree G p i) :
    orderedNonedgeSum G p ≤ orderedNonedgeSum G (massMove p i j) := by
  rw [orderedNonedgeSum_massMove G p hij]
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) (hp j))
    (sub_nonneg.mpr hdeg))

end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.MassTransfer

-- BEGIN TSEProof.IndependentSupport
section

namespace TensorNP.SymEigen.TSEFresh

noncomputable section
open scoped BigOperators
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem sum_massSupport (p : V → ℝ) : ∑ i ∈ massSupport p, p i = ∑ i, p i := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  by_contra hp
  exact hi (by simpa using hp)

omit [DecidableEq V] in
theorem sum_sq_massSupport (p : V → ℝ) :
    ∑ i ∈ massSupport p, (p i) ^ 2 = ∑ i, (p i) ^ 2 := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hp : p i = 0 := by simpa using hi
  simp [hp]

theorem nonedge_term_of_independent (G : SimpleGraph V) (p : V → ℝ)
    (hI : G.IsIndepSet (massSupport p : Set V)) (i j : V) :
    nonedgeCoeff G i j * p i * p j = p i * p j - if i = j then (p i) ^ 2 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [pow_two]
  · by_cases hi : p i = 0
    · simp [hi, hij]
    · by_cases hj : p j = 0
      · simp [hj, hij]
      · have hn : ¬ G.Adj i j := hI (by simpa using hi) (by simpa using hj) hij
        simp [nonedgeCoeff, hij, hn]

theorem orderedNonedgeSum_of_independent (G : SimpleGraph V) (p : V → ℝ)
    (hI : G.IsIndepSet (massSupport p : Set V)) :
    orderedNonedgeSum G p = (∑ i, p i) ^ 2 - ∑ i, (p i) ^ 2 := by
  simp only [orderedNonedgeSum, nonedgeBilin, nonedge_term_of_independent G p hI,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum,
    ← Finset.sum_mul, pow_two]

theorem independent_support_bound (G : SimpleGraph V) (p : V → ℝ)
    (hI : G.IsIndepSet (massSupport p : Set V)) :
    (G.indepNum : ℝ) * orderedNonedgeSum G p ≤
      ((G.indepNum : ℝ) - 1) * (∑ i, p i) ^ 2 := by
  have hc : ((massSupport p).card : ℝ) ≤ (G.indepNum : ℝ) := by
    exact_mod_cast hI.card_le_indepNum
  have hsq : 0 ≤ ∑ i, (p i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (p i))
  have hcs := sq_sum_le_card_mul_sum_sq (s := massSupport p) (f := p)
  rw [sum_massSupport, sum_sq_massSupport] at hcs
  have hle := mul_le_mul_of_nonneg_right hc hsq
  rw [orderedNonedgeSum_of_independent G p hI]
  nlinarith

end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.IndependentSupport

-- BEGIN TSEProof.MotzkinStraus
section

namespace TensorNP.SymEigen.TSEFresh

noncomputable section
open scoped BigOperators
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ordered_motzkin_straus (G : SimpleGraph V) (p : V → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    (G.indepNum : ℝ) * orderedNonedgeSum G p ≤
      ((G.indepNum : ℝ) - 1) * (∑ i, p i) ^ 2 := by
  have main : ∀ n : ℕ, ∀ q : V → ℝ, (massSupport q).card = n →
      (∀ i, 0 ≤ q i) →
      (G.indepNum : ℝ) * orderedNonedgeSum G q ≤
        ((G.indepNum : ℝ) - 1) * (∑ i, q i) ^ 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hcard hq
      by_cases hI : G.IsIndepSet (massSupport q : Set V)
      · exact independent_support_bound G q hI
      · have hex : ∃ i ∈ massSupport q, ∃ j ∈ massSupport q, G.Adj i j := by
          by_contra h
          apply hI
          intro i hi j hj _ hadj
          exact h ⟨i, hi, j, hj, hadj⟩
        obtain ⟨i, hi, j, hj, hij⟩ := hex
        have step : ∀ a b : V, a ∈ massSupport q → b ∈ massSupport q →
            G.Adj a b → nonedgeDegree G q b ≤ nonedgeDegree G q a →
            (G.indepNum : ℝ) * orderedNonedgeSum G q ≤
              ((G.indepNum : ℝ) - 1) * (∑ i, q i) ^ 2 := by
          intro a b ha hb hab hdeg
          have hlt : (massSupport (massMove q a b)).card < n := by
            rw [← hcard]
            exact massMove_support_card_lt q hab.ne (by simpa using ha) (by simpa using hb)
          have hnew := ih _ hlt (massMove q a b) rfl (massMove_nonneg q hq hab.ne)
          rw [massMove_sum] at hnew
          exact le_trans
            (mul_le_mul_of_nonneg_left (orderedNonedgeSum_massMove_le G q hq hab hdeg)
              (Nat.cast_nonneg G.indepNum)) hnew
        rcases le_total (nonedgeDegree G q j) (nonedgeDegree G q i) with hdeg | hdeg
        · exact step i j hi hj hij hdeg
        · exact step j i hj hi hij.symm hdeg
  exact main _ p rfl hp

end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.MotzkinStraus

-- BEGIN TSEProof.NormalizedMotzkinStraus
section

namespace TensorNP.SymEigen.TSEFresh

open scoped BigOperators

 theorem ordered_motzkin_straus_div {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p : V → ℝ) (hp : ∀ i, 0 ≤ p i)
    (ha : 0 < G.indepNum) :
    orderedNonedgeSum G p ≤ (1 - 1 / (G.indepNum : ℝ)) * (∑ i, p i) ^ 2 := by
  have har : (0 : ℝ) < G.indepNum := by exact_mod_cast ha
  have h := ordered_motzkin_straus G p hp
  apply (mul_le_mul_iff_right₀ har).mp
  calc
    (G.indepNum : ℝ) * orderedNonedgeSum G p ≤
        ((G.indepNum : ℝ) - 1) * (∑ i, p i) ^ 2 := h
    _ = (G.indepNum : ℝ) * ((1 - 1 / (G.indepNum : ℝ)) * (∑ i, p i) ^ 2) := by
      rw [← mul_assoc, mul_sub, mul_one, mul_one_div, div_self (ne_of_gt har)]

end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.NormalizedMotzkinStraus

-- BEGIN TSEProof.PairQuadratic
section

namespace TensorNP.SymEigen.TSEFresh

noncomputable section
open Classical
open scoped BigOperators

 theorem pair_square_sum_twice {v : ℕ} (G : SimpleGraph (Fin v)) (x : Fin v → ℝ) :
    2 * (∑ p : PairIdx v, if ¬ G.Adj p.1.1 p.1.2 then
      (x p.1.1) ^ 2 * (x p.1.2) ^ 2 else 0) =
        orderedNonedgeSum G (fun i => (x i) ^ 2) := by
  let f : Fin v → Fin v → ℝ := fun i j => if ¬ G.Adj i j then (x i)^2 * (x j)^2 else 0
  calc
    _ = ∑ p : PairIdx v, (f p.1.1 p.1.2 + f p.1.2 p.1.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      dsimp only [f]
      rw [G.adj_comm p.1.2 p.1.1]
      split_ifs <;> ring
    _ = ∑ i, ∑ j, if i ≠ j then f i j else 0 := sum_pairs_both f
    _ = orderedNonedgeSum G (fun i => (x i)^2) := by
      rw [orderedNonedgeSum_eq]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [f]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]

 theorem pair_cauchy {v : ℕ} (G : SimpleGraph (Fin v)) (x : Fin v → ℝ)
    (y : PairIdx v → ℝ) :
    (∑ p : PairIdx v, if ¬ G.Adj p.1.1 p.1.2 then x p.1.1 * x p.1.2 * y p else 0)^2 ≤
      (∑ p : PairIdx v, if ¬ G.Adj p.1.1 p.1.2 then
        (x p.1.1)^2 * (x p.1.2)^2 else 0) * ∑ p, (y p)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : PairIdx v => if ¬ G.Adj p.1.1 p.1.2 then x p.1.1 * x p.1.2 else 0) y
  simpa only [ite_mul, zero_mul, ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_pow] using h

 theorem cubic_scalar_optimization (s t : ℝ) (hs : 0 ≤ s) (hst : s + t = 1) :
    s^2 * t ≤ 4 / 27 := by
  have h := mul_nonneg (sq_nonneg (s - 2 / 3)) (show 0 ≤ s + 1 / 3 by linarith)
  have ht : t = 1 - s := by linarith
  rw [ht]
  nlinarith

end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.PairQuadratic

-- BEGIN TSEProof.EigenCubic
section
namespace TensorNP.SymEigen.TSEFresh
open scoped BigOperators

theorem cubic_as_contractions {ι : Type*} [Fintype ι] (A : Tensor3 ι) (x : ι → ℝ) :
    cubicForm A x = ∑ k, (∑ i, ∑ j, A i j k * x i * x j) * x k := by
  symm
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem unit_square_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) (h : l2norm x=1) :
    ∑ i, x i ^ 2 = 1 := by
  have hn : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hs := Real.sq_sqrt hn
  rw [←l2norm, h] at hs
  norm_num at hs ⊢
  exact hs.symm

theorem eigenvalue_eq_cubic {ι : Type*} [Fintype ι] (A : Tensor3 ι) (lam : ℝ)
    (x : ι → ℝ) (hu : l2norm x=1)
    (he : ∀ k, (∑ i, ∑ j, A i j k * x i * x j)=lam*x k) :
    cubicForm A x=lam := by
  rw [cubic_as_contractions]
  simp_rw [he, mul_assoc, ←sq]
  rw [←Finset.mul_sum, unit_square_sum x hu, mul_one]
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.EigenCubic

-- BEGIN TSEProof.CubicFormula
section
namespace TensorNP.SymEigen.TSEFresh
open Classical
open scoped BigOperators
noncomputable section
variable {v : ℕ}

theorem cubic_eq_pair_sum (G : SimpleGraph (Fin v)) (z : Idx v → ℝ) :
    cubicForm (stabTensor G) z = 6 * ∑ p : PairIdx v,
      if ¬G.Adj p.1.1 p.1.2 then
        z (.inl p.1.1)*z (.inl p.1.2)*z (.inr p) else 0 := by
  rw [cubic_as_contractions, Fintype.sum_sum_type]
  simp_rw [contraction_vertex, contraction_pair]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : ¬G.Adj p.1.1 p.1.2
  · simp [h, add_mul, mul_add, ite_mul, mul_ite, Finset.sum_add_distrib]
    ring
  · simp [h]
end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.CubicFormula

-- BEGIN TSEProof.CubicBound
section

namespace TensorNP.SymEigen.TSEFresh

noncomputable section
open Classical
open scoped BigOperators

 theorem indepNum_pos {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) : 1 ≤ G.indepNum := by
  let i : Fin v := ⟨0, hv⟩
  have hI : G.IsIndepSet (({i} : Finset (Fin v)) : Set (Fin v)) := by
    simp [SimpleGraph.IsIndepSet]
  simpa using hI.card_le_indepNum

 theorem cubic_sq_bound {v : ℕ} (G : SimpleGraph (Fin v)) (ha : 1 ≤ G.indepNum)
    (z : Idx v → ℝ) (hz : l2norm z = 1) :
    (cubicForm (stabTensor G) z)^2 ≤ (8 / 3 : ℝ) * (1 - 1 / (G.indepNum : ℝ)) := by
  let x : Fin v → ℝ := fun i => z (.inl i)
  let y : PairIdx v → ℝ := fun p => z (.inr p)
  let s : ℝ := ∑ i, (x i)^2
  let t : ℝ := ∑ p, (y p)^2
  let q : ℝ := ∑ p : PairIdx v, if ¬ G.Adj p.1.1 p.1.2 then (x p.1.1)^2*(x p.1.2)^2 else 0
  let b : ℝ := ∑ p : PairIdx v, if ¬ G.Adj p.1.1 p.1.2 then x p.1.1*x p.1.2*y p else 0
  let c : ℝ := 1 - 1 / (G.indepNum : ℝ)
  have hs : 0 ≤ s := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have ht : 0 ≤ t := Finset.sum_nonneg (fun p _ => sq_nonneg (y p))
  have hst : s + t = 1 := by
    simpa only [s, t, x, y, Fintype.sum_sum_type] using unit_square_sum z hz
  have har : (1 : ℝ) ≤ G.indepNum := by exact_mod_cast ha
  have hap : (0 : ℝ) < G.indepNum := lt_of_lt_of_le (by norm_num) har
  have hc : 0 ≤ c := sub_nonneg.mpr ((div_le_one hap).mpr har)
  have hcs : b^2 ≤ q*t := pair_cauchy G x y
  have hms : 2*q ≤ c*s^2 := by
    have h := ordered_motzkin_straus_div G (fun i => (x i)^2)
      (fun i => sq_nonneg (x i)) (Nat.lt_of_lt_of_le (by decide : 0 < 1) ha)
    rw [← pair_square_sum_twice G x] at h
    exact h
  have htwo := mul_le_mul_of_nonneg_right hms ht
  have hopt := mul_le_mul_of_nonneg_left (cubic_scalar_optimization s t hs hst) hc
  rw [cubic_eq_pair_sum]
  change (6*b)^2 ≤ (8 / 3 : ℝ) * c
  nlinarith

end
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.CubicBound

-- BEGIN TSEProof.EigenvalueUpper
section

namespace TensorNP.SymEigen.TSEFresh

 theorem eigenvalue_index_le {v l : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v))
    (hl : 1 ≤ l) (he : IsUnitL2Eigenvalue (stabTensor G) (lambdaL l)) : l ≤ G.indepNum := by
  obtain ⟨z, hz, he⟩ := he
  have ha := indepNum_pos hv G
  have h := cubic_sq_bound G ha z hz
  rw [eigenvalue_eq_cubic (stabTensor G) (lambdaL l) z hz he] at h
  exact lambda_index_le hl ha h

end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.EigenvalueUpper

-- BEGIN TSEProof.NativeConclusion
section
namespace TensorNP.SymEigen.TSEFresh

theorem native_theorem_9_3_core {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) :
    IsGreatest {l : ℕ | 1 ≤ l ∧ l ≤ v ∧ IsUnitL2Eigenvalue (stabTensor G) (lambdaL l)}
      G.indepNum := by
  classical
  have ha := indepNum_pos hv G
  obtain ⟨S,hS⟩ := G.exists_isNIndepSet_indepNum
  have hav : G.indepNum ≤ v := by
    rw [←hS.card_eq]
    exact le_trans (Finset.card_le_univ S) (by simp)
  refine ⟨⟨ha,hav,?_⟩,?_⟩
  · by_cases h1 : G.indepNum=1
    · rw [h1]
      exact zero_eigenvalue hv G
    · have h2 : 2 ≤ S.card := by rw [hS.card_eq]; omega
      simpa only [hS.card_eq] using independent_set_eigenvalue G S hS.isIndepSet h2
  · intro l hl
    exact eigenvalue_index_le hv G hl.1 hl.2.2
end TensorNP.SymEigen.TSEFresh
end
-- END TSEProof.NativeConclusion

-- BEGIN TSEProof.FinalRoot
section

namespace TensorNP.SymEigen

theorem theorem_9_3_core {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) :
    IsGreatest {l : ℕ | 1 ≤ l ∧ l ≤ v ∧ IsUnitL2Eigenvalue (stabTensor G) (lambdaL l)}
      G.indepNum := by
  exact TSEFresh.native_theorem_9_3_core hv G

end TensorNP.SymEigen
end
-- END TSEProof.FinalRoot

theorem solution {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) :
    IsGreatest {l : ℕ | 1 ≤ l ∧ l ≤ v ∧ TensorNP.SymEigen.IsUnitL2Eigenvalue (TensorNP.SymEigen.stabTensor G) (TensorNP.SymEigen.lambdaL l)}
      G.indepNum := by
  exact TensorNP.SymEigen.theorem_9_3_core hv G
