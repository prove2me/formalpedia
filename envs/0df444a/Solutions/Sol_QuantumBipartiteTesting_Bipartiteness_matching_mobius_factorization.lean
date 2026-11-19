-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.matching_mobius_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:39:18.884575+00:00
-- url     : https://prove2.me/submissions/2c64a1b8-b134-4be8-97fb-490f0efcd58f

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_partition_power_sum_cancellation
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Homogenize

namespace QuantumBipartiteTesting.Bipartiteness.MatchingProof
noncomputable section
open Finset Polynomial
open scoped Pointwise
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private def SumPoly (a : ℕ) : ℚ[X] :=
  C (1/(a+1:ℚ))*(Polynomial.bernoulli (a+1)-C (_root_.bernoulli (a+1)))

private lemma bern_degree (a : ℕ) : (Polynomial.bernoulli a).natDegree ≤ a := by
  rw [Polynomial.bernoulli]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le a i)

private lemma sumPoly_degree (a : ℕ) : (SumPoly a).natDegree ≤ a+1 := by
  unfold SumPoly
  apply le_trans Polynomial.natDegree_mul_le
  simp only [Polynomial.natDegree_C,zero_add]
  simpa only [max_self] using
    (Polynomial.natDegree_sub_le_of_le (m := a+1) (n := a+1) (bern_degree _) (by simp))

private lemma sumPoly_zero (a : ℕ) : (SumPoly a).eval 0 = 0 := by
  simp [SumPoly,Polynomial.bernoulli_eval_zero]

private lemma sumPoly_eval (a n : ℕ) : (SumPoly a).eval (n:ℚ) = ∑ s ∈ range n, (s:ℚ)^a := by
  have hh := Polynomial.sum_range_pow_eq_bernoulli_sub n a
  simp only [SumPoly,eval_mul,eval_C,eval_sub]
  rw [← hh]
  field_simp

private def OddPolyQ (a : ℕ) : ℚ[X] :=
  (SumPoly a).comp (C 2*X) - C (2^a)*(SumPoly a)

private lemma oddPolyQ_degree (a : ℕ) : (OddPolyQ a).natDegree ≤ a+1 := by
  unfold OddPolyQ
  have hcomp : ((SumPoly a).comp (C 2*X)).natDegree ≤ a+1 :=
    Polynomial.natDegree_comp_le.trans (by simpa using sumPoly_degree a)
  have hmul : (C (2^a)*(SumPoly a)).natDegree ≤ a+1 := by
    apply le_trans Polynomial.natDegree_mul_le
    simpa using sumPoly_degree a
  simpa only [max_self] using Polynomial.natDegree_sub_le_of_le hcomp hmul

private lemma oddPolyQ_zero (a : ℕ) : (OddPolyQ a).eval 0 = 0 := by
  simp [OddPolyQ,sumPoly_zero]

private lemma even_odd_sum (f : ℕ → ℚ) (n : ℕ) :
    (∑ s ∈ range (2*n), f s) = (∑ s ∈ range n, f (2*s)) + ∑ s ∈ range n, f (2*s+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,ih,
      Finset.sum_range_succ,Finset.sum_range_succ]
    ring

private lemma oddPolyQ_eval (a n : ℕ) :
    (OddPolyQ a).eval (n:ℚ) = ∑ s ∈ range n, (2*(s:ℚ)+1)^a := by
  have hh := even_odd_sum (fun s => (s:ℚ)^a) n
  have he : (∑ s ∈ range n, ((2*s:ℕ):ℚ)^a) = (2:ℚ)^a * ∑ s ∈ range n, (s:ℚ)^a := by
    simp only [Nat.cast_mul,Nat.cast_ofNat,mul_pow,Finset.mul_sum]
  have ho : (∑ s ∈ range n, ((2*s+1:ℕ):ℚ)^a) = ∑ s ∈ range n, (2*(s:ℚ)+1)^a := by simp
  rw [he,ho] at hh
  unfold OddPolyQ
  simp only [eval_sub,eval_comp,eval_mul,eval_C,eval_X]
  rw [show (2:ℚ)*(n:ℚ) = ((2*n:ℕ):ℚ) by norm_cast,sumPoly_eval,sumPoly_eval]
  linarith

private def OddPoly (a : ℕ) : ℝ[X] := (OddPolyQ a).map (Rat.castHom ℝ)

private lemma oddPoly_degree (a : ℕ) : (OddPoly a).natDegree ≤ a+1 :=
  (Polynomial.natDegree_map_le).trans (oddPolyQ_degree a)

private lemma oddPoly_zero (a : ℕ) : (OddPoly a).eval 0 = 0 := by
  rw [OddPoly,eval_map]
  have hh := Polynomial.eval₂_at_apply (p := OddPolyQ a) (Rat.castHom ℝ) 0
  simpa [oddPolyQ_zero] using hh

private lemma oddPoly_eval (a n : ℕ) :
    (OddPoly a).eval (n:ℝ) = ∑ s ∈ range n, (2*(s:ℝ)+1)^a := by
  have hh := congrArg (fun x : ℚ => (x:ℝ)) (oddPolyQ_eval a n)
  rw [OddPoly,eval_map]
  rw [show (n:ℝ) = (Rat.castHom ℝ) (n:ℚ) by simp,Polynomial.eval₂_at_apply]
  simpa using hh

private lemma multiset_newton (s : Multiset ℝ) (n : ℕ) :
    (n:ℝ)*s.esymm n = (-1:ℝ)^(n+1) *
      ∑ a ∈ (antidiagonal n).filter (fun a => a.1 < n),
        (-1:ℝ)^a.1 * s.esymm a.1 * (s.map (fun x => x^a.2)).sum := by
  have hpow (a : ℕ) : (∑ x : s, (x:ℝ)^a) = (s.map (fun x => x^a)).sum := by
    exact congrArg Multiset.sum (Multiset.map_univ s (fun x : ℝ => x^a))
  have hh := congrArg (MvPolynomial.aeval (fun x : s => (x:ℝ)))
    (MvPolynomial.mul_esymm_eq_sum s ℝ n)
  simpa only [map_mul,map_pow,map_neg,map_one,map_natCast,map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm,Multiset.map_univ_coe,
    MvPolynomial.psum,MvPolynomial.aeval_X,hpow] using hh

private def PS {k colors : ℕ} (d : Fin k → Fin colors → ℝ) (a : ℕ) : Partition k → ℝ :=
  fun p => ∑ S ∈ Blocks p, ∑ j : Fin colors, (∑ i ∈ S, d i j)^a

private def Generators {k colors : ℕ} (d : Fin k → Fin colors → ℝ) (n : ℕ) :
    Set (Partition k → ℝ) :=
  {f | ∃ m : ℕ, ∃ a : Fin m → ℕ, (∀ t, 0 < a t) ∧ (∑ t, (a t-1)) ≤ n ∧
    f = fun r => ∏ t : Fin m, PS d (a t) r}

private def Filtration {k colors : ℕ} (d : Fin k → Fin colors → ℝ) (n : ℕ) :
    Submodule ℝ (Partition k → ℝ) := Submodule.span ℝ (Generators d n)

private lemma filtration_mono {k colors : ℕ} (d : Fin k → Fin colors → ℝ) {n m : ℕ} (h : n ≤ m) :
    Filtration d n ≤ Filtration d m := by
  apply Submodule.span_mono
  rintro f ⟨t,a,ha,hs,rfl⟩
  exact ⟨t,a,ha,hs.trans h,rfl⟩

private lemma filtration_one {k colors : ℕ} (d : Fin k → Fin colors → ℝ) (n : ℕ) :
    (1 : Partition k → ℝ) ∈ Filtration d n := by
  apply Submodule.subset_span
  exact ⟨0,Fin.elim0,by intro t; exact t.elim0,by simp,by ext r; simp⟩

private lemma filtration_const {k colors : ℕ} (d : Fin k → Fin colors → ℝ) (n : ℕ) (c : ℝ) :
    (fun _ : Partition k => c) ∈ Filtration d n := by
  have heq : (fun _ : Partition k => c) = c • (1 : Partition k → ℝ) := by ext r; simp
  rw [heq]
  exact (Filtration d n).smul_mem c (filtration_one d n)

private lemma filtration_powerSum {k colors : ℕ} (d : Fin k → Fin colors → ℝ) (a : ℕ) (ha : 0 < a) :
    PS d a ∈ Filtration d (a-1) := by
  apply Submodule.subset_span
  refine ⟨1,fun _ => a,fun _ => ha,?_,?_⟩
  · simp
  · ext r
    simp

private lemma generators_mul {k colors : ℕ} (d : Fin k → Fin colors → ℝ) (n m : ℕ) :
    (Generators d n)*(Generators d m) ⊆ Generators d (n+m) := by
  rintro f ⟨g,hg,h,hh,rfl⟩
  obtain ⟨t,a,ha,hs,rfl⟩ := hg
  obtain ⟨u,b,hb,ht,rfl⟩ := hh
  refine ⟨t+u,Fin.addCases a b,?_,?_,?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using ha j
    · simpa using hb j
  · rw [Fin.sum_univ_add]
    simpa using Nat.add_le_add hs ht
  · ext r
    rw [Fin.prod_univ_add]
    simp

private lemma filtration_mul {k colors : ℕ} (d : Fin k → Fin colors → ℝ) (n m : ℕ) :
    (Filtration d n)*(Filtration d m) ≤ Filtration d (n+m) := by
  unfold Filtration
  rw [Submodule.span_mul_span]
  exact Submodule.span_mono (generators_mul d n m)

private lemma filtration_mul_mem {k colors : ℕ} (d : Fin k → Fin colors → ℝ) {n m : ℕ}
    {f g : Partition k → ℝ} (hf : f ∈ Filtration d n) (hg : g ∈ Filtration d m) :
    f*g ∈ Filtration d (n+m) :=
  filtration_mul d n m (Submodule.mul_mem_mul hf hg)

private def MuLinear {k : ℕ} (p : Partition k) : (Partition k → ℝ) →ₗ[ℝ] ℝ :=
  ∑ r : Partition k, if Refines r p then (Mobius r p:ℝ) • LinearMap.proj r else 0

private lemma muLinear_apply {k : ℕ} (p : Partition k) (f : Partition k → ℝ) :
    MuLinear p f = ∑ r : Partition k, if Refines r p then (Mobius r p:ℝ)*f r else 0 := by
  simp only [MuLinear,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> simp

private lemma filtration_cancel {k colors : ℕ} (p : Partition k) (d : Fin k → Fin colors → ℝ)
    (n : ℕ) (hn : n+(Blocks p).card < k) {f : Partition k → ℝ} (hf : f ∈ Filtration d n) :
    MuLinear p f = 0 := by
  have hle : Filtration d n ≤ LinearMap.ker (MuLinear p) := by
    apply Submodule.span_le.mpr
    rintro g ⟨m,a,ha,hs,rfl⟩
    change MuLinear p (fun r => ∏ t, PS d (a t) r) = 0
    rw [muLinear_apply]
    exact partition_power_sum_cancellation p a ha d (by omega)
  exact LinearMap.mem_ker.mp (hle hf)

private def Aggregate {k colors : ℕ} (d : Fin k → Fin colors → ℝ) (P : ℝ[X]) : Partition k → ℝ :=
  fun r => ∑ S ∈ Blocks r, ∑ j : Fin colors, P.eval (∑ i ∈ S, d i j)

private lemma aggregate_mem {k colors : ℕ} (d : Fin k → Fin colors → ℝ) (P : ℝ[X])
    (a : ℕ) (hP : P.natDegree ≤ a+1) (h0 : P.eval 0 = 0) : Aggregate d P ∈ Filtration d a := by
  have heq : Aggregate d P = ∑ b ∈ range (P.natDegree+1), (P.coeff b) • PS d b := by
    ext r
    simp only [Aggregate,Polynomial.eval_eq_sum_range,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,PS]
    simp_rw [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S hS
    conv_rhs => rw [Finset.sum_comm]
  rw [heq]
  apply (Filtration d a).sum_mem
  intro b hb
  by_cases hb0 : b = 0
  · subst b
    have hc : P.coeff 0 = 0 := by simpa only [Polynomial.coeff_zero_eq_eval_zero] using h0
    simp only [hc,zero_smul]
    exact (Filtration d a).zero_mem
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    have hw : b-1 ≤ a := by have hh := mem_range.mp hb; omega
    exact (Filtration d a).smul_mem _ (filtration_mono d hw (filtration_powerSum d b hbpos))

private def PatternNaturals {k colors : ℕ} (d : Fin k → Fin colors → ℕ) (r : Partition k) : Multiset ℕ :=
  (Blocks r).val.bind fun S => (univ : Finset (Fin colors)).val.bind fun j =>
    ((range (∑ i ∈ S, d i j)).val.map fun a => 2*a+1)

private def PatternNumbers {k colors : ℕ} (d : Fin k → Fin colors → ℕ) (r : Partition k) : Multiset ℝ :=
  (PatternNaturals d r).map (fun a => (a:ℝ))

private lemma pattern_powerSum {k colors : ℕ} (d : Fin k → Fin colors → ℕ) (a : ℕ) (r : Partition k) :
    ((PatternNumbers d r).map (fun x => x^a)).sum =
      Aggregate (fun i j => (d i j:ℝ)) (OddPoly a) r := by
  unfold PatternNumbers PatternNaturals Aggregate
  simp only [Multiset.bind_def,Multiset.pure_def,Multiset.fmap_def,Multiset.bind_singleton,
    Multiset.map_bind,Multiset.sum_bind,Multiset.map_map,Function.comp_apply,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  change (∑ S ∈ Blocks r, ∑ j : Fin colors, ∑ b ∈ range (∑ i ∈ S, d i j), (2*(b:ℝ)+1)^a) = _
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [Nat.cast_sum] using (oddPoly_eval a (∑ i ∈ S, d i j)).symm

private lemma pattern_powerSum_mem {k colors : ℕ} (d : Fin k → Fin colors → ℕ) (a : ℕ) :
    (fun r => ((PatternNumbers d r).map (fun x => x^a)).sum) ∈
      Filtration (fun i j => (d i j:ℝ)) a := by
  have heq : (fun r => ((PatternNumbers d r).map (fun x => x^a)).sum) =
      Aggregate (fun i j => (d i j:ℝ)) (OddPoly a) := by funext r; exact pattern_powerSum d a r
  rw [heq]
  exact aggregate_mem _ _ a (oddPoly_degree a) (oddPoly_zero a)

private def ComplementPower {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (a : ℕ) : Partition k → ℝ := fun r => ((B-PatternNumbers d r).map (fun x => x^a)).sum

private lemma complement_power_mem {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (hB : ∀ r, PatternNumbers d r ≤ B) (a : ℕ) :
    ComplementPower B d a ∈ Filtration (fun i j => (d i j:ℝ)) a := by
  have heq : ComplementPower B d a = (fun _ => (B.map (fun x => x^a)).sum) -
      (fun r => ((PatternNumbers d r).map (fun x => x^a)).sum) := by
    ext r
    have hh := congrArg (fun s : Multiset ℝ => (s.map (fun x => x^a)).sum)
      (Multiset.sub_add_cancel (hB r))
    rw [Multiset.map_add,Multiset.sum_add] at hh
    exact eq_sub_of_add_eq hh
  rw [heq]
  exact (Filtration _ a).sub_mem (filtration_const _ _ _) (pattern_powerSum_mem d a)

private def ComplementEsymm {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (n : ℕ) : Partition k → ℝ := fun r => (B-PatternNumbers d r).esymm n

private lemma complement_esymm_mem {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (hB : ∀ r, PatternNumbers d r ≤ B) (n : ℕ) :
    ComplementEsymm B d n ∈ Filtration (fun i j => (d i j:ℝ)) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      have heq : ComplementEsymm B d 0 = (1 : Partition k → ℝ) := by
        ext r
        simp [ComplementEsymm,Multiset.esymm]
      rw [heq]
      exact filtration_one (fun i j => (d i j:ℝ)) 0
    have hnpos : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    let S := (antidiagonal n).filter fun a => a.1 < n
    have heq : (n:ℝ) • ComplementEsymm B d n = (-1:ℝ)^(n+1) •
        (∑ a ∈ S, (-1:ℝ)^a.1 • (ComplementEsymm B d a.1 * ComplementPower B d a.2)) := by
      ext r
      simpa [ComplementEsymm,ComplementPower,S,mul_assoc] using multiset_newton (B-PatternNumbers d r) n
    have hsum : (∑ a ∈ S, (-1:ℝ)^a.1 • (ComplementEsymm B d a.1 * ComplementPower B d a.2)) ∈
        Filtration (fun i j => (d i j:ℝ)) n := by
      apply (Filtration _ n).sum_mem
      intro a ha
      obtain ⟨ha,hlt⟩ := mem_filter.mp ha
      have hsum := mem_antidiagonal.mp ha
      apply (Filtration _ n).smul_mem
      have hh := filtration_mul_mem _ (ih a.1 hlt) (complement_power_mem B d hB a.2)
      simpa only [hsum] using hh
    have hscaled : (n:ℝ) • ComplementEsymm B d n ∈ Filtration (fun i j => (d i j:ℝ)) n := by
      rw [heq]
      exact (Filtration _ n).smul_mem _ hsum
    have hh := (Filtration (fun i j => (d i j:ℝ)) n).smul_mem ((n:ℝ)⁻¹) hscaled
    simpa only [smul_smul,inv_mul_cancel₀ hnpos.ne',one_smul] using hh

private lemma complement_esymm_cancel {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (hB : ∀ r, PatternNumbers d r ≤ B) (p : Partition k) (n : ℕ)
    (hn : n+(Blocks p).card < k) :
    (∑ r : Partition k, if Refines r p then
      (Mobius r p:ℝ)*(B-PatternNumbers d r).esymm n else 0) = 0 := by
  have hh := filtration_cancel p (fun i j => (d i j:ℝ)) n hn (complement_esymm_mem B d hB n)
  simpa only [muLinear_apply,ComplementEsymm] using hh

private lemma sum_blocks {k : ℕ} (r : Partition k) (f : Fin k → ℕ) :
    (∑ S ∈ Blocks r, ∑ i ∈ S, f i) = ∑ i, f i := by
  let s : Setoid (Fin k) := ⟨fun i j => r.val i j = true,r.property⟩
  let P := Finpartition.ofSetoid s
  have hparts : P.parts = Blocks r := by
    simp only [P,Finpartition.ofSetoid,Finpartition.ofSetSetoid_parts,Blocks]
    congr 1
    funext a
    ext b
    simp only [mem_filter,mem_univ,true_and]
    rfl
  calc
    _ = ∑ S ∈ P.parts, ∑ i ∈ S, f i := by rw [hparts]
    _ = ∑ i ∈ P.parts.biUnion id, f i := (Finset.sum_biUnion P.supIndep.pairwiseDisjoint).symm
    _ = _ := by rw [P.biUnion_parts]

private lemma pattern_card {k colors : ℕ} (d : Fin k → Fin colors → ℕ) (r : Partition k) :
    (PatternNumbers d r).card = ∑ i, ∑ j, d i j := by
  unfold PatternNumbers PatternNaturals
  simp only [Multiset.bind_def,Multiset.pure_def,Multiset.bind_singleton,
    Multiset.card_map,Multiset.card_bind,Function.comp_apply]
  change (∑ S ∈ Blocks r, ∑ j : Fin colors, (range (∑ i ∈ S, d i j)).card) = _
  simp only [card_range]
  rw [Finset.sum_comm]
  simp_rw [sum_blocks]
  rw [Finset.sum_comm]

private lemma blocks_card_le {k : ℕ} (p : Partition k) : (Blocks p).card ≤ k := by
  unfold Blocks
  exact Finset.card_image_le.trans_eq (by simp)

private def Numerator {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (p : Partition k) : ℝ[X] :=
  ∑ r : Partition k, if Refines r p then
    C (Mobius r p:ℝ)*((B-PatternNumbers d r).map (fun a => X-C a)).prod else 0

private lemma numerator_degree {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (hB : ∀ r, PatternNumbers d r ≤ B) (p : Partition k) :
    (Numerator B d p).natDegree ≤ B.card-(∑ i, ∑ j, d i j) := by
  unfold Numerator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r hr
  split_ifs
  · apply le_trans Polynomial.natDegree_mul_le
    simp only [Polynomial.natDegree_C,zero_add,Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
    rw [Multiset.card_sub (hB r),pattern_card]
  · simp

private lemma numerator_coeff {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (hB : ∀ r, PatternNumbers d r ≤ B) (p : Partition k) (n : ℕ)
    (hn : n ≤ B.card-(∑ i, ∑ j, d i j)) :
    (Numerator B d p).coeff n =
      (-1:ℝ)^(B.card-(∑ i, ∑ j, d i j)-n) *
        MuLinear p (ComplementEsymm B d (B.card-(∑ i, ∑ j, d i j)-n)) := by
  rw [muLinear_apply]
  unfold Numerator
  rw [Polynomial.finsetSum_coeff,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs
  · simp only [Polynomial.coeff_C_mul,ComplementEsymm]
    have hc : (B-PatternNumbers d r).card = B.card-(∑ i, ∑ j, d i j) := by
      rw [Multiset.card_sub (hB r),pattern_card]
    rw [Multiset.prod_X_sub_C_coeff _ (by simpa only [hc] using hn),hc]
    ring
  · simp

private lemma numerator_coeff_vanish {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (hB : ∀ r, PatternNumbers d r ≤ B) (p : Partition k) (n : ℕ)
    (hn : B.card-(∑ i, ∑ j, d i j)-n+(Blocks p).card < k) :
    (Numerator B d p).coeff n = 0 := by
  by_cases hle : n ≤ B.card-(∑ i, ∑ j, d i j)
  · rw [numerator_coeff B d hB p n hle]
    have hz := filtration_cancel p (fun i j => (d i j:ℝ)) _ hn
      (complement_esymm_mem B d hB (B.card-(∑ i, ∑ j, d i j)-n))
    rw [hz,mul_zero]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((numerator_degree B d hB p).trans_lt (lt_of_not_ge hle))

private lemma numerator_degree_drop {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (hB : ∀ r, PatternNumbers d r ≤ B) (p : Partition k) :
    (Numerator B d p).natDegree ≤ B.card-(∑ i, ∑ j, d i j)-(k-(Blocks p).card) := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hhigh : B.card-(∑ i, ∑ j, d i j) < n
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((numerator_degree B d hB p).trans_lt hhigh)
  · apply numerator_coeff_vanish B d hB p n
    have hb := blocks_card_le p
    omega

private lemma numerator_zero {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (hB : ∀ r, PatternNumbers d r ≤ B) (p : Partition k)
    (hsmall : B.card-(∑ i, ∑ j, d i j) < k-(Blocks p).card) :
    Numerator B d p = 0 := by
  ext n
  simp only [Polynomial.coeff_zero]
  apply numerator_coeff_vanish B d hB p n
  have hb := blocks_card_le p
  omega

private def CommonNaturals (q : ℕ) : Multiset ℕ :=
  (range (2*q)).val.bind fun a => Multiset.replicate (2*q/(a+1)) (2*a+1)

private def CommonNumbers (q : ℕ) : Multiset ℝ :=
  (CommonNaturals q).map (fun a => (a:ℝ))

private lemma odd_injective : Function.Injective (fun a : ℕ => 2*a+1) := by
  intro a b h
  dsimp at h
  omega

private lemma odd_range_count (a n : ℕ) :
    Multiset.count (2*a+1) ((range n).val.map (fun b => 2*b+1)) = if a < n then 1 else 0 := by
  rw [Multiset.count_map_eq_count' _ _ odd_injective]
  simpa only [Finset.mem_val,Finset.mem_range] using
    (Multiset.count_eq_of_nodup (range n).nodup : Multiset.count a (range n).val = _)

private lemma common_count (q a : ℕ) :
    Multiset.count (2*a+1) (CommonNaturals q) = 2*q/(a+1) := by
  unfold CommonNaturals
  rw [Multiset.count_bind]
  change (∑ b ∈ range (2*q), Multiset.count (2*a+1) (Multiset.replicate (2*q/(b+1)) (2*b+1))) = _
  simp only [Multiset.count_replicate,show ∀ b, (2*b+1 = 2*a+1) ↔ b = a from fun b => ⟨fun h => odd_injective h,fun h => h ▸ rfl⟩]
  by_cases ha : a < 2*q
  · simp [ha]
  · have hz : 2*q/(a+1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [ha,hz]

private lemma pattern_count {k colors : ℕ} (d : Fin k → Fin colors → ℕ) (r : Partition k) (a : ℕ) :
    Multiset.count (2*a+1) (PatternNaturals d r) =
      ∑ S ∈ Blocks r, ∑ j : Fin colors, if a < ∑ i ∈ S, d i j then 1 else 0 := by
  unfold PatternNaturals
  simp only [Multiset.count_bind]
  change (∑ S ∈ Blocks r, ∑ j : Fin colors,
    Multiset.count (2*a+1) ((range (∑ i ∈ S, d i j)).val.map (fun b => 2*b+1))) = _
  simp only [odd_range_count]

private lemma pattern_naturals_le_common {k colors : ℕ} (d : Fin k → Fin colors → ℕ) (q : ℕ)
    (he : (∑ i, ∑ j, d i j) ≤ 2*q) (r : Partition k) : PatternNaturals d r ≤ CommonNaturals q := by
  apply Multiset.le_iff_count.mpr
  intro x
  by_cases hx : x ∈ PatternNaturals d r
  · obtain ⟨S,hS,j,hj,a,ha,hx⟩ : ∃ S ∈ Blocks r, ∃ j : Fin colors, j ∈ univ ∧
        ∃ a ∈ range (∑ i ∈ S, d i j), 2*a+1 = x := by
      simpa only [PatternNaturals,Multiset.mem_bind,Finset.mem_val,Multiset.mem_map] using hx
    subst x
    rw [pattern_count,common_count,Nat.le_div_iff_mul_le (Nat.succ_pos a),Finset.sum_mul]
    calc
      _ ≤ ∑ S ∈ Blocks r, ∑ j : Fin colors, ∑ i ∈ S, d i j := by
        apply sum_le_sum
        intro S hS
        rw [Finset.sum_mul]
        apply sum_le_sum
        intro j hj
        split_ifs with h
        · simp only [one_mul]; omega
        · simp
      _ = ∑ i, ∑ j, d i j := by
        rw [Finset.sum_comm]
        simp_rw [sum_blocks]
        rw [Finset.sum_comm]
      _ ≤ _ := he
  · rw [Multiset.count_eq_zero_of_notMem hx]
    exact Nat.zero_le _

private lemma pattern_le_common {k colors : ℕ} (d : Fin k → Fin colors → ℕ) (q : ℕ)
    (he : (∑ i, ∑ j, d i j) ≤ 2*q) (r : Partition k) : PatternNumbers d r ≤ CommonNumbers q := by
  simpa only [PatternNumbers,CommonNumbers,Multiset.bind_def,Multiset.pure_def,Multiset.bind_singleton,Multiset.map_id'] using
    (Multiset.map_le_map (f := fun a : ℕ => (a:ℝ)) (pattern_naturals_le_common d q he r))

private lemma common_card (q : ℕ) : (CommonNumbers q).card = DenominatorDegree q := by
  unfold CommonNumbers CommonNaturals DenominatorDegree
  simp only [Multiset.bind_def,Multiset.pure_def,Multiset.bind_singleton,Multiset.card_map,Multiset.card_bind,Function.comp_apply,Multiset.card_replicate]
  rfl

private def RootProduct (s : Multiset ℝ) : ℝ[X] :=
  (s.map (fun a => X-C a)).prod

private lemma rootProduct_add (s t : Multiset ℝ) :
    RootProduct (s+t) = RootProduct s*RootProduct t := by
  simp only [RootProduct,Multiset.map_add,Multiset.prod_add]

private lemma rootProduct_sub_mul {s B : Multiset ℝ} (h : s ≤ B) :
    RootProduct (B-s)*RootProduct s = RootProduct B := by
  rw [← rootProduct_add,Multiset.sub_add_cancel h]

private lemma rootProduct_sub_mul_eval {s B : Multiset ℝ} (h : s ≤ B) (t : ℝ) :
    (RootProduct (B-s)).eval t*(RootProduct s).eval t = (RootProduct B).eval t := by
  rw [← Polynomial.eval_mul,rootProduct_sub_mul h]

private lemma numerator_rational {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (hB : ∀ r, PatternNumbers d r ≤ B) (p : Partition k) (t : ℝ)
    (ht : (RootProduct B).eval t ≠ 0) :
    (Numerator B d p).eval t / (RootProduct B).eval t =
      ∑ r : Partition k, if Refines r p then
        (Mobius r p:ℝ)/(RootProduct (PatternNumbers d r)).eval t else 0 := by
  unfold Numerator
  rw [Polynomial.eval_finset_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs
  · simp only [eval_mul,eval_C]
    have hmul := rootProduct_sub_mul_eval (hB r) t
    have hk : (RootProduct (PatternNumbers d r)).eval t ≠ 0 := by
      intro h
      rw [h,mul_zero] at hmul
      exact ht hmul.symm
    apply (div_eq_div_iff ht hk).mpr
    change (Mobius r p:ℝ)*(RootProduct (B-PatternNumbers d r)).eval t * _ = _
    rw [mul_assoc,hmul]
  · simp

private lemma homogenize_numerator {k colors : ℕ} (B : Multiset ℝ) (d : Fin k → Fin colors → ℕ)
    (hB : ∀ r, PatternNumbers d r ≤ B) (p : Partition k) :
    ∃ H : Bivariate, H.totalDegree ≤ B.card ∧ ∀ t l : ℝ, l ≠ 0 →
      l^B.card * (Numerator B d p).eval t =
        l^((∑ i, ∑ j, d i j)+k-(Blocks p).card) * Eval H (l*t) l := by
  let e := ∑ i, ∑ j, d i j
  let b := (Blocks p).card
  have hb : b ≤ k := blocks_card_le p
  have he : e ≤ B.card := by
    have hh := Multiset.card_le_card (hB p)
    rwa [pattern_card] at hh
  by_cases hz : B.card-e < k-b
  · refine ⟨0,by simp,?_⟩
    intro t l hl
    simp only [numerator_zero B d hB p hz,Polynomial.eval_zero,mul_zero,Eval,map_zero]
  · let n := B.card-e-(k-b)
    refine ⟨(Numerator B d p).homogenize n,?_,?_⟩
    · exact (Polynomial.isHomogeneous_homogenize (Numerator B d p)).totalDegree_le.trans (by dsimp [n]; omega)
    · intro t l hl
      have hh := Polynomial.eval_homogenize (numerator_degree_drop B d hB p) ![l*t,l] hl
      have heval : Eval ((Numerator B d p).homogenize n) (l*t) l =
          (Numerator B d p).eval t*l^n := by
        simpa only [Eval,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
          mul_div_cancel_left₀ t hl] using hh
      rw [heval]
      have hn : B.card = (e+k-b)+n := by dsimp [n]; omega
      rw [hn,pow_add]
      ring

private lemma matchingMoment_reciprocal (n : ℕ) (M l : ℝ) (hl : l ≠ 0) :
    MatchingMoment n M l =
      ((RootProduct ((range n).val.map (fun a => (2*(a:ℝ)+1)))).eval (M/l))⁻¹ := by
  unfold MatchingMoment RootProduct
  simp only [Multiset.bind_def,Multiset.pure_def,Multiset.bind_singleton,Multiset.map_id,
    Polynomial.eval_multiset_prod,Multiset.map_map,Function.comp_apply,eval_sub,eval_X,eval_C]
  change (∏ a ∈ range n, l/(M-((2*(a+1)-1:ℕ):ℝ)*l)) =
    (∏ a ∈ range n, (M/l-(2*(a:ℝ)+1)))⁻¹
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro a ha
  have hc : ((2*(a+1)-1:ℕ):ℝ) = 2*(a:ℝ)+1 := by
    rw [show 2*(a+1)-1 = 2*a+1 by omega]
    push_cast
    rfl
  rw [hc]
  have he : M/l-(2*(a:ℝ)+1) = (M-(2*(a:ℝ)+1)*l)/l := by field_simp
  rw [he,inv_div]


private lemma partitionMoment_reciprocal {k colors : ℕ} (d : Fin k → Fin colors → ℕ)
    (r : Partition k) (M l : ℝ) (hl : l ≠ 0) :
    (∏ S ∈ Blocks r, ∏ j : Fin colors, MatchingMoment (∑ i ∈ S, d i j) M l) =
      ((RootProduct (PatternNumbers d r)).eval (M/l))⁻¹ := by
  unfold RootProduct PatternNumbers PatternNaturals
  simp only [Multiset.bind_def,Multiset.pure_def,Multiset.bind_singleton,Multiset.map_id,
    Multiset.map_bind,Multiset.prod_bind,Multiset.map_map,Function.comp_apply,
    Polynomial.eval_multiset_prod,eval_sub,eval_X,eval_C,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  change (∏ S ∈ Blocks r, ∏ j : Fin colors, MatchingMoment (∑ i ∈ S, d i j) M l) =
    (∏ S ∈ Blocks r, ∏ j : Fin colors, ∏ a ∈ range (∑ i ∈ S, d i j), (M/l-(2*(a:ℝ)+1)))⁻¹
  simp_rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro S hS
  apply Finset.prod_congr rfl
  intro j hj
  have hh := matchingMoment_reciprocal (∑ i ∈ S, d i j) M l hl
  simp only [RootProduct,Multiset.bind_def,Multiset.pure_def,Multiset.bind_singleton,
    Polynomial.eval_multiset_prod,Multiset.map_map,Function.comp_apply,eval_sub,eval_X,eval_C] at hh
  change MatchingMoment (∑ i ∈ S, d i j) M l =
    (∏ a ∈ range (∑ i ∈ S, d i j), (M/l-(2*(a:ℝ)+1)))⁻¹ at hh
  simpa only [Finset.prod_inv_distrib] using hh

private lemma common_eval (q : ℕ) (t : ℝ) :
    (RootProduct (CommonNumbers q)).eval t =
      ∏ a ∈ range (2*q), (t-(2*(a:ℝ)+1))^(2*q/(a+1)) := by
  unfold RootProduct CommonNumbers CommonNaturals
  simp only [Multiset.bind_def,Multiset.pure_def,Multiset.bind_singleton,Multiset.map_id',
    Multiset.map_bind,Multiset.prod_bind,Multiset.map_map,Function.comp_apply,
    Polynomial.eval_multiset_prod,eval_sub,eval_X,eval_C,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
    Multiset.map_replicate,Multiset.prod_replicate,eval_pow,eval_sub,eval_X,eval_C]
  rfl

private lemma denominator_common (q : ℕ) (M l : ℝ) (hl : l ≠ 0) :
    Eval (Denominator q) M l = l^DenominatorDegree q * (RootProduct (CommonNumbers q)).eval (M/l) := by
  rw [common_eval]
  unfold Eval Denominator DenominatorDegree
  simp only [map_prod,map_pow,map_sub,MvPolynomial.eval_X,map_mul,MvPolynomial.eval_C,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  have hf (a : ℕ) : (M-((2*(a+1)-1:ℕ):ℝ)*l) = l*(M/l-(2*(a:ℝ)+1)) := by
    have hc : ((2*(a+1)-1:ℕ):ℝ) = 2*(a:ℝ)+1 := by
      rw [show 2*(a+1)-1 = 2*a+1 by omega]
      push_cast
      rfl
    rw [hc]
    field_simp
    <;> ring
  simp_rw [hf,mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

end
end QuantumBipartiteTesting.Bipartiteness.MatchingProof

open QuantumBipartiteTesting.Bipartiteness
open QuantumBipartiteTesting.Bipartiteness.MatchingProof
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

theorem solution {k colors : ℕ} (d : Fin k → Fin colors → ℕ) (q : ℕ)
    (he : (∑ i, ∑ j, d i j) ≤ 2*q) (p : Partition k) :
    ∃ H : Bivariate, H.totalDegree ≤ DenominatorDegree q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        (∑ r : Partition k, if Refines r p then (Mobius r p:ℝ) *
          (∏ S ∈ Blocks r, ∏ j : Fin colors, MatchingMoment (∑ i ∈ S, d i j) M l) else 0) =
        l^((∑ i, ∑ j, d i j)+k-(Blocks p).card) * Eval H M l / Eval (Denominator q) M l := by
  have hB := pattern_le_common d q he
  obtain ⟨H,hdeg,hH⟩ := homogenize_numerator (CommonNumbers q) d hB p
  refine ⟨H,by simpa only [common_card] using hdeg,?_⟩
  intro M l hl hD
  have hden := denominator_common q M l hl
  have hc : (RootProduct (CommonNumbers q)).eval (M/l) ≠ 0 := by
    intro h
    rw [h,mul_zero] at hden
    exact hD hden
  have hrat := numerator_rational (CommonNumbers q) d hB p (M/l) hc
  simp_rw [partitionMoment_reciprocal d _ M l hl] 
  rw [← show (Numerator (CommonNumbers q) d p).eval (M/l) /
      (RootProduct (CommonNumbers q)).eval (M/l) =
      ∑ r : Partition k, if Refines r p then (Mobius r p:ℝ) *
        ((RootProduct (PatternNumbers d r)).eval (M/l))⁻¹ else 0 by
    simpa only [div_eq_mul_inv] using hrat]
  apply (div_eq_div_iff hc hD).mpr
  have hh := hH (M/l) l hl
  have hm : l*(M/l) = M := by field_simp
  rw [hm,common_card] at hh
  rw [hden]
  calc
    _ = (l^DenominatorDegree q * (Numerator (CommonNumbers q) d p).eval (M/l)) *
      (RootProduct (CommonNumbers q)).eval (M/l) := by ring
    _ = _ := by rw [hh]
end
