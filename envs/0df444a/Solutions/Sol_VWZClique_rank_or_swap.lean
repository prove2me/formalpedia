-- Prove2me | solution 1 for VWZClique.rank_or_swap
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T01:21:53.308821+00:00
-- url     : https://prove2.me/submissions/405a5342-7242-4aaf-88f9-950015917d54

import Definitions.Def_VWZClique_Operators

open VWZClique
namespace VWZClique.RankSwap

/-- The three one-coordinate operators used in the interpolation argument. -/
inductive Factor where
  | identity | swap | difference
  deriving DecidableEq

def factorEntry (o : Factor) (s u v t : Bool) : ℚ :=
  let id : ℚ := if s = v ∧ u = t then 1 else 0
  let swap : ℚ := if s = t ∧ u = v then 1 else 0
  match o with
  | .identity => id
  | .swap => swap
  | .difference => id - swap

def inverseNormSq (j : Fin 4) : ℚ := if j < 2 then 1 else 1/2

def eigenvalue (o : Factor) (j : Fin 4) : ℚ :=
  match o with
  | .identity => 1
  | .swap => if j = 3 then -1 else 1
  | .difference => if j = 3 then 2 else 0

theorem oneBit_resolution : ∀ (o : Factor) (s u v t : Bool),
    factorEntry o s u v t = ∑ j : Fin 4,
      (eigenvalue o j * inverseNormSq j) * oneBit j s u * oneBit j v t := by
  intro o
  cases o <;> decide +kernel

/-- An arbitrary tensor word in I, P, and I-P, expanded in exactly the
unnormalized product basis of the submitted rank-or-swap statement. -/
theorem tensor_resolution {L : ℕ} (o : Fin L → Factor) (x y : PairBits L) :
    (∏ i, factorEntry (o i) (x.1 i) (x.2 i) (y.1 i) (y.2 i)) =
    ∑ j : BasisLabel L, (∏ i, eigenvalue (o i) (j i) * inverseNormSq (j i)) *
      basisEntry j x * basisEntry j y := by
  simp_rw [oneBit_resolution]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [basisEntry, Finset.prod_mul_distrib]

theorem identity_resolution {L : ℕ} (x y : PairBits L) :
    (if x = y then (1 : ℚ) else 0) = ∑ j : BasisLabel L,
      (∏ i, inverseNormSq (j i)) * basisEntry j x * basisEntry j y := by
  classical
  have h := tensor_resolution (fun _ : Fin L => .identity) x y
  simp only [eigenvalue, one_mul] at h
  rw [← h]
  by_cases hxy : x = y
  · subst y
    simp [factorEntry]
  · rw [if_neg hxy]
    symm
    apply Finset.prod_eq_zero_iff.mpr
    obtain ⟨i,hi⟩ : ∃ i, ¬ (x.1 i = y.1 i ∧ x.2 i = y.2 i) := by
      by_contra! hh
      exact hxy (Prod.ext (funext fun i => (hh i).1) (funext fun i => (hh i).2))
    exact ⟨i, Finset.mem_univ _, by simp [factorEntry, hi]⟩

/-- The four signed matrix units of I-P, in row/column bit order. -/
def unitBits (i : ℕ) : Bool × Bool × Bool × Bool :=
  if i = 0 then (false,true,false,true)
  else if i = 1 then (true,false,true,false)
  else if i = 2 then (false,true,true,false)
  else (true,false,false,true)

def localMatch (b : Option (Bool × Bool × Bool × Bool)) (s u v t : Bool) : Prop :=
  match b with
  | none => s = t ∧ u = v
  | some a => (s,u,v,t) = a

instance (b : Option (Bool × Bool × Bool × Bool)) (s u v t : Bool) :
    Decidable (localMatch b s u v t) := by cases b <;> unfold localMatch <;> infer_instance

def maskBit (active : Bool) (i : ℕ) := if active then some (unitBits i) else none
def signBit (active : Bool) (i : ℕ) : ℤ := if active && decide (2 ≤ i) then -1 else 1
abbrev choices (active : Bool) : ℕ := if active then 4 else 1

theorem local_units (active s u v t : Bool) :
    factorEntry (if active then .difference else .swap) s u v t =
    ∑ k : Fin (choices active), (signBit active k.val : ℚ) *
      (if localMatch (maskBit active k.val) s u v t then 1 else 0) := by
  cases active
  · cases s <;> cases u <;> cases v <;> cases t <;>
      norm_num [factorEntry, signBit, maskBit, localMatch]
  · have four (f : Fin (choices true) → ℚ) :
        ∑ k, f k = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four f
    rw [four]
    cases s <;> cases u <;> cases v <;> cases t <;>
      norm_num [factorEntry, signBit, maskBit, unitBits, localMatch, choices]

theorem mask_product {L : ℕ} (m : Mask L) (x y : PairBits L) :
    (∏ i, (if localMatch (m i) (x.1 i) (x.2 i) (y.1 i) (y.2 i) then (1 : ℚ) else 0))
      = swapEntry m x y := by
  classical
  by_cases hs : swapOK m x y
  · rw [swapEntry, if_pos hs]
    exact Finset.prod_eq_one fun i _ => if_pos (hs i)
  · rw [swapEntry, if_neg hs]
    apply Finset.prod_eq_zero_iff.mpr
    change ¬ (∀ i, localMatch (m i) (x.1 i) (x.2 i) (y.1 i) (y.2 i)) at hs
    obtain ⟨i, hi⟩ := not_forall.mp hs
    exact ⟨i, Finset.mem_univ _, if_neg hi⟩

/-- A tensor word with h difference factors expands into 4^h signed partial
swaps. Each element of the dependent index type is one term of this sum. -/
theorem word_to_partial_swaps {L : ℕ} (a : Fin L → Bool) (x y : PairBits L) :
    (∏ i, factorEntry (if a i then .difference else .swap) (x.1 i) (x.2 i) (y.1 i) (y.2 i)) =
    ∑ k : (∀ i, Fin (choices (a i))),
      ((∏ i, signBit (a i) (k i).val : ℤ) : ℚ) * swapEntry (fun i => maskBit (a i) (k i).val) x y := by
  simp_rw [local_units]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.prod_mul_distrib, ← mask_product, Int.cast_prod]

theorem word_term_count {L : ℕ} (a : Fin L → Bool) :
    Fintype.card (∀ i, Fin (choices (a i))) = 4 ^ (Finset.univ.filter fun i => a i = true).card := by
  rw [Fintype.card_pi]
  calc
    _ = ∏ i, choices (a i) := Finset.prod_congr rfl fun i _ => Fintype.card_fin _
    _ = _ := by simp [choices, ← Finset.prod_filter]

end VWZClique.RankSwap

open VWZClique
open scoped BigOperators
namespace VWZClique.RankSwap

/-- Translation by one in the binomial basis scaled by powers of -2. -/
def shift (c : ℕ → ℤ) (h : ℕ) : ℤ := c h - 2 * c (h+1)

private def backSum (c : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | n+1, h => c h + 2 * backSum c n (h+1)

theorem shift_preimage {d : ℕ} (c : ℕ → ℤ) (hc : ∀ h > d, c h = 0) :
    ∃ b : ℕ → ℤ, (∀ h > d, b h = 0) ∧ shift b = c := by
  let b := fun h => backSum c (d+1-h) h
  refine ⟨b, ?_, ?_⟩
  · intro h hh
    simp [b, show d+1-h=0 by omega, backSum]
  · funext h
    by_cases hh : h ≤ d
    · have n : d+1-h = (d+1-(h+1))+1 := by omega
      simp only [shift, b, n, backSum]
      ring
    · simp [shift, b, show d+1-h=0 by omega, show d+1-(h+1)=0 by omega, backSum,
        hc h (by omega)]

theorem shift_constant {c : ℕ → ℤ} (n : ℕ) (v : ℤ) (h : ∀ i ≤ n, c i = v) :
    (shift^[n] c) 0 = (-1)^n * v := by
  induction n generalizing c v with
  | zero => simpa using h 0 (by omega)
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hs : ∀ i ≤ n, shift c i = -v := by
      intro i hi
      rw [shift, h i (by omega), h (i+1) (by omega)]
      ring
    rw [ih (-v) hs, pow_succ]
    ring

/-- An integral interpolant that has the prescribed parity on a whole interval.
Repeated inverse translations preserve the cutoff in the binomial basis. -/
theorem integer_window (a d : ℕ) :
    ∃ c : ℕ → ℤ, (∀ h > d, c h = 0) ∧
      ∀ t ≤ d, (shift^[a+t] c) 0 = (-1)^(a+t) := by
  let base := fun h => if h ≤ d then (-1:ℤ)^a else 0
  have back (k : ℕ) : ∃ c : ℕ → ℤ, (∀ h > d, c h = 0) ∧ (shift^[k]) c = base := by
    induction k with
    | zero => exact ⟨base, fun h hh => if_neg (by omega), rfl⟩
    | succ k ih =>
      obtain ⟨c,hc,hi⟩ := ih
      obtain ⟨b,hb,hs⟩ := shift_preimage c hc
      exact ⟨b,hb,by rwa [Function.iterate_succ_apply, hs]⟩
  obtain ⟨c,hc,hi⟩ := back a
  refine ⟨c,hc,?_⟩
  intro t ht
  rw [Nat.add_comm a t, Function.iterate_add_apply, hi, shift_constant t ((-1)^a), pow_add]
  intro i hi
  exact if_pos (by omega)

theorem subset_evaluation {ι : Type*} (B : Finset ι) (c : ℕ → ℤ) (u : ℕ) :
    ∑ S ∈ B.powerset, (-2 : ℤ)^S.card * c (u + S.card) = (shift^[B.card] c) u := by
  classical
  induction B using Finset.induction_on generalizing c with
  | empty => simp
  | @insert b B hb ih =>
    rw [Finset.card_insert_of_notMem hb, Function.iterate_succ_apply, ← ih]
    rw [Finset.sum_powerset_insert hb, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    have hnot : b ∉ S := fun h => hb (Finset.mem_powerset.mp hS h)
    rw [Finset.card_insert_of_notMem hnot, pow_succ, shift]
    simp only [Nat.add_assoc]
    ring

end VWZClique.RankSwap

open VWZClique
namespace VWZClique.RankSwap

def antisymmetric {L : ℕ} (j : BasisLabel L) : Finset (Fin L) :=
  Finset.univ.filter fun i => j i = 3

def smallSets (L d : ℕ) : Finset (Finset (Fin L)) := Finset.univ.filter fun S => S.card ≤ d

def outside (L a d : ℕ) : Finset (BasisLabel L) := Finset.univ.filter fun j =>
  ¬ (a ≤ (antisymmetric j).card ∧ (antisymmetric j).card ≤ a+d)

def active {L : ℕ} (S : Finset (Fin L)) (i : Fin L) : Bool := decide (i ∈ S)
def op {L : ℕ} (S : Finset (Fin L)) (i : Fin L) : Factor :=
  if active S i then .difference else .swap

def spec {L : ℕ} (S : Finset (Fin L)) (j : BasisLabel L) : ℚ := ∏ i, eigenvalue (op S i) (j i)

theorem word_eigenvalue {L : ℕ} (S : Finset (Fin L)) (j : BasisLabel L) :
    spec S j = (-1 : ℚ)^(antisymmetric j).card *
      (if S ⊆ antisymmetric j then (-2 : ℚ)^S.card else 0) := by
  classical
  have each (i : Fin L) : eigenvalue (op S i) (j i) =
      (if i ∈ antisymmetric j then (-1 : ℚ) else 1) *
      (if i ∈ S then (if i ∈ antisymmetric j then -2 else 0) else 1) := by
    by_cases hi : i ∈ S <;> by_cases hj : j i = 3 <;> simp [op, active, eigenvalue, hi, hj, antisymmetric]
  simp only [spec, each, Finset.prod_mul_distrib, Fintype.prod_ite_mem, Finset.prod_const]
  congr 1
  by_cases hs : S ⊆ antisymmetric j
  · rw [if_pos hs, ← Finset.prod_const]
    exact Finset.prod_congr rfl fun i hi => if_pos (hs hi)
  · rw [if_neg hs]
    obtain ⟨i,hi,hn⟩ := Finset.not_subset.mp hs
    exact Finset.prod_eq_zero hi (if_neg hn)

theorem aggregate_eigenvalue {L d : ℕ} (j : BasisLabel L) (c : ℕ → ℤ) (hc : ∀ h > d, c h = 0) :
    ∑ S ∈ smallSets L d, (c S.card : ℚ) * spec S j =
    ((-1 : ℤ)^(antisymmetric j).card * (shift^[(antisymmetric j).card] c) 0 : ℤ) := by
  classical
  let B := antisymmetric j
  have full : ∑ S ∈ smallSets L d, (c S.card : ℚ) * spec S j =
      ∑ S : Finset (Fin L), (c S.card : ℚ) * spec S j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro S _ h
    have hh : d < S.card := by simpa [smallSets] using h
    simp [hc _ hh]
  rw [full]
  simp_rw [word_eigenvalue]
  change (∑ S : Finset (Fin L), (c S.card : ℚ) * ((-1)^B.card * (if S ⊆ B then (-2)^S.card else 0))) = _
  have single (S : Finset (Fin L)) : (c S.card : ℚ) *
        ((-1)^B.card * (if S ⊆ B then (-2)^S.card else 0)) =
      (-1)^B.card * (if S ∈ B.powerset then (-2 : ℚ)^S.card * c S.card else 0) := by
    by_cases hs : S ⊆ B <;> simp [hs, Finset.mem_powerset] <;> ring
  simp_rw [single]
  rw [← Finset.mul_sum, Finset.sum_ite_mem]
  have hs := subset_evaluation B c 0
  simp only [zero_add] at hs
  push_cast
  change _ = (-1:ℚ)^B.card * ((shift^[B.card] c) 0 : ℤ)
  rw [← hs]
  push_cast
  simp

abbrev Terms (L d : ℕ) := (S : ↥(smallSets L d)) × ((i : Fin L) → Fin (choices (active S.val i)))

def termMask {L d : ℕ} (t : Terms L d) : Mask L := fun i => maskBit (active t.1.val i) (t.2 i).val
def termCoeff {L d : ℕ} (c : ℕ → ℤ) (t : Terms L d) : ℤ :=
  c t.1.val.card * ∏ i, signBit (active t.1.val i) (t.2 i).val

theorem terms_card (L d : ℕ) : Fintype.card (Terms L d) = ∑ S ∈ smallSets L d, 4^S.card := by
  rw [Fintype.card_sigma]
  simp_rw [word_term_count]
  simp [active]
  exact Finset.sum_attach _ (fun S : Finset (Fin L) => 4 ^ S.card)

def normWeight {L : ℕ} (j : BasisLabel L) := ∏ i, inverseNormSq (j i)

theorem two_expansions {L d : ℕ} (c : ℕ → ℤ) (x y : PairBits L) :
    (∑ j : BasisLabel L, (∑ S ∈ smallSets L d, (c S.card : ℚ) * spec S j) *
      normWeight j * basisEntry j x * basisEntry j y) =
    ∑ t : Terms L d, (termCoeff c t : ℚ) * swapEntry (termMask t) x y := by
  classical
  have word (S : Finset (Fin L)) :
      ∑ j : BasisLabel L, spec S j * normWeight j * basisEntry j x * basisEntry j y =
      ∑ k : (∀ i, Fin (choices (active S i))),
        ((∏ i, signBit (active S i) (k i).val : ℤ) : ℚ) *
          swapEntry (fun i => maskBit (active S i) (k i).val) x y := by
    have h := tensor_resolution (op S) x y
    simp only [Finset.prod_mul_distrib] at h
    exact h.symm.trans (word_to_partial_swaps (active S) x y)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Fintype.sum_sigma]
  rw [← Finset.sum_attach (smallSets L d) (fun S => ∑ j : BasisLabel L,
    (c S.card : ℚ) * spec S j * normWeight j * basisEntry j x * basisEntry j y)]
  apply Finset.sum_congr rfl
  intro S _
  simp only [termCoeff, Int.cast_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  unfold termMask
  convert! (word S.val) using 1 <;> simp only [mul_assoc]

/-- Exact finite-dimensional decomposition for any integer interpolation window. -/
theorem finite_window (L a d : ℕ) :
    ∃ (m : Fin (Fintype.card (Terms L d)) → Mask L)
      (c : Fin (Fintype.card (Terms L d)) → ℤ) (r : BasisLabel L → ℚ),
    ∀ x y : PairBits L, (if x = y then (1 : ℚ) else 0) =
      (∑ j ∈ outside L a d, r j * basisEntry j x * basisEntry j y) +
      ∑ i, (c i : ℚ) * swapEntry (m i) x y := by
  classical
  obtain ⟨c, hc, hint⟩ := integer_window a d
  let e := (Fintype.equivFin (Terms L d)).symm
  let coeff := fun (j : BasisLabel L) => ∑ S ∈ smallSets L d, (c S.card : ℚ) * spec S j
  let r := fun j => (1 - coeff j) * normWeight j
  refine ⟨fun i => termMask (e i), fun i => termCoeff c (e i), r, ?_⟩
  intro x y
  have small : ∑ j ∈ outside L a d, r j * basisEntry j x * basisEntry j y =
      ∑ j, r j * basisEntry j x * basisEntry j y := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have range : a ≤ (antisymmetric j).card ∧ (antisymmetric j).card ≤ a+d := by simpa [outside] using hj
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le range.1
    have val := aggregate_eigenvalue j c hc
    rw [ht, hint t (by omega), ← mul_pow] at val
    norm_num at val
    change (1-_) * _ * _ * _ = _
    simp [coeff, val]
  rw [small, e.sum_comp (fun t => (termCoeff c t : ℚ) * swapEntry (termMask t) x y),
    ← two_expansions, identity_resolution, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change normWeight j * _ * _ = (1 - coeff j) * normWeight j * _ * _ +
    coeff j * normWeight j * _ * _
  ring

end VWZClique.RankSwap

open Filter Topology Real
namespace VWZClique.RankSwap

/-- One-coordinate exponential moment, centered at a proposed tail cutoff p. -/
noncomputable def moment (s p t : ℝ) : ℝ := (3 + exp (s*t)) * exp (-(p*s)*t)

theorem moment_pos (s p t : ℝ) : 0 < moment s p t := by unfold moment; positivity

theorem improving_tilt (s p : ℝ) (hp : s * (1 - 4*p) < 0) :
    ∃ t : ℝ, 0 < t ∧ moment s p t < 4 := by
  have h₁ := ((hasDerivAt_const (0 : ℝ) (3 : ℝ)).add
    (((hasDerivAt_id (0 : ℝ)).const_mul s).exp))
  have h₂ := (((hasDerivAt_id (0 : ℝ)).const_mul (-(p*s))).exp)
  have hd : HasDerivAt (moment s p) (s*(1-4*p)) 0 := by
    convert! h₁.mul h₂ using 1 <;> simp [moment] <;> ring
  have hh := hd.tendsto_slope_zero_right.eventually_lt_const hp
  have pos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  obtain ⟨t, ht, h⟩ := (pos.and hh).exists
  have ht' : 0 < t := ht
  simp only [zero_add, smul_eq_mul, moment, mul_zero, exp_zero, mul_one] at h
  exact ⟨t, ht', by
    unfold moment
    by_contra! hn
    exact (not_lt_of_ge (mul_nonneg (inv_pos.mpr ht').le (by linarith))) h⟩

theorem positive_near_zero {f : ℝ → ℝ} {B : ℝ} (hf : ContinuousAt f 0) (h : f 0 < B) :
    ∃ x : ℝ, 0 < x ∧ x < 1/4 ∧ f x < B := by
  have hh : ∀ᶠ x in 𝓝[>] (0 : ℝ), f x < B :=
    (hf.eventually_lt_const h).filter_mono nhdsWithin_le_nhds
  have hx : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1/4 :=
    (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)).filter_mono nhdsWithin_le_nhds
  have pos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  exact (pos.and (hx.and hh)).exists

theorem sparse_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ t η : ℝ, 0 < t ∧ 0 < η ∧ η < 1/4 ∧
      (1+4*exp (-t))*exp (3*t*η) < (2:ℝ)^ε := by
  have lim : Tendsto (fun t : ℝ => 1+4*exp (-t)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_exp_neg_atTop_nhds_zero) :
      Tendsto (fun t : ℝ => 1+4*exp (-t)) atTop (𝓝 (1+4*0)))
  have eps : 1 < (2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  obtain ⟨t,ht,ht'⟩ := ((eventually_gt_atTop (0 : ℝ)).and (lim.eventually_lt_const eps)).exists
  obtain ⟨η,hη,hη',h⟩ := positive_near_zero (f := fun x => (1+4*exp (-t))*exp (3*t*x))
    (by fun_prop) (B := (2:ℝ)^ε) (by simpa using ht')
  exact ⟨t,η,ht,hη,hη',h⟩

theorem combine_tails {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hu' : u < 4) (hv' : v < 4) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ L : ℕ in atTop, u^L+v^L ≤ ((2:ℝ)^(2-δ))^L := by
  let b := max u v
  have hb : 0 < b := lt_of_lt_of_le hu (le_max_left _ _)
  have hbc : b < 4 := max_lt hu' hv'
  obtain ⟨δ,hδ,_,h⟩ := positive_near_zero (f := fun x : ℝ => -((2:ℝ)^(2-x))) (B := -b)
    (by simp_rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]; fun_prop) (by norm_num; linarith)
  let B := (2:ℝ)^(2-δ)
  have hB : 0 < B := by dsimp [B]; positivity
  have hlt : b < B := by dsimp [B]; linarith
  have lim := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hb.le hB.le) ((div_lt_one hB).mpr hlt)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [lim.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with L hL
  rw [div_pow, div_lt_iff₀ (pow_pos hB L)] at hL
  have h1 := pow_le_pow_left₀ hu.le (le_max_left u v) L
  have h2 := pow_le_pow_left₀ hv.le (le_max_right u v) L
  change u^L + v^L ≤ B^L
  dsimp [b] at hL
  linarith

theorem pow_comm (L : ℕ) (p : ℝ) : ((2:ℝ)^L)^p = ((2:ℝ)^p)^L := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul_natCast (by norm_num)]

end VWZClique.RankSwap

open VWZClique Real Filter Topology
namespace VWZClique.RankSwap

theorem sparse_bound (L d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (Fintype.card (Terms L d) : ℝ) ≤ (1 + 4*exp (-t))^L * exp (t*d) := by
  classical
  rw [terms_card, Nat.cast_sum]
  push_cast
  have gen : ∑ S : Finset (Fin L), (4*exp (-t))^S.card = (1+4*exp (-t))^L := by
    simpa only [one_pow, mul_one, Fintype.card_fin, add_comm (4*exp (-t)) 1]
      using Fintype.sum_pow_mul_eq_add_pow (Fin L) (4*exp (-t)) 1
  rw [← gen, Finset.sum_mul]
  calc
    _ ≤ ∑ S ∈ smallSets L d, (4*exp (-t))^S.card * exp (t*d) := by
      apply Finset.sum_le_sum
      intro S hS
      have hs : S.card ≤ d := (Finset.mem_filter.mp hS).2
      have hs' : (0:ℝ) ≤ (S.card : ℝ)*(-t) + t*d := by
        have := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hs : (S.card : ℝ) ≤ d) ht
        linarith
      rw [mul_pow, mul_assoc, ← exp_nat_mul, ← exp_add]
      exact le_mul_of_one_le_right (by positivity) (one_le_exp hs')
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => by positivity)

theorem type_generating (L : ℕ) (v : ℝ) :
    ∑ j : BasisLabel L, (exp v)^(antisymmetric j).card = (3+exp v)^L := by
  have coord (j : BasisLabel L) : (exp v)^(antisymmetric j).card =
      ∏ i, if j i = 3 then exp v else 1 := by simp [antisymmetric, ← Finset.prod_filter]
  simp_rw [coord]
  rw [← Fintype.prod_sum (fun (_ : Fin L) (k : Fin 4) => if k = 3 then exp v else 1)]
  have bit : (∑ k : Fin 4, if k = 3 then exp v else 1) = 3 + exp v := by
    rw [Fin.sum_univ_four]
    norm_num [show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 3 by decide,
      show (2 : Fin 4) ≠ 3 by decide]
  simp [bit]

noncomputable def tilted {L : ℕ} (s p t : ℝ) (j : BasisLabel L) :=
  exp (s*t * ((antisymmetric j).card - p*L))

theorem sum_tilted (L : ℕ) (s p t : ℝ) : ∑ j : BasisLabel L, tilted s p t j = (moment s p t)^L := by
  have term (j : BasisLabel L) : tilted s p t j =
      (exp (s*t))^(antisymmetric j).card * (exp (-(p*s)*t))^L := by
    unfold tilted
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
    congr 1
    ring
  simp_rw [term]
  rw [← Finset.sum_mul, type_generating, ← mul_pow, moment]

/-- Bound both tails by their tilted generating functions. -/
theorem both_tails (L : ℕ) (p q u v : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q)
    (hu : 0 < u) (hv : 0 < v) :
    let a := ⌊p*L⌋₊
    let b := ⌊q*L⌋₊
    ((outside L a (b-a)).card : ℝ) ≤ (moment (-1) p u)^L + (moment 1 q v)^L := by
  classical
  intro a b
  have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_right hpq (by positivity))
  let T := outside L a (b-a)
  change (T.card : ℝ) ≤ _
  rw [← sum_tilted, ← sum_tilted, ← Finset.sum_add_distrib]
  calc
    (T.card : ℝ) = ∑ _ ∈ T, (1 : ℝ) := by simp
    _ ≤ ∑ j ∈ T, (tilted (-1) p u j + tilted 1 q v j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hout : ¬ (a ≤ (antisymmetric j).card ∧ (antisymmetric j).card ≤ b) := by
        simpa [T, outside, Nat.add_sub_of_le hab, Nat.add_comm a (b-a)] using hj
      by_cases hj' : a ≤ (antisymmetric j).card
      · have hj'' : b < (antisymmetric j).card := by omega
        have hqL : 0 ≤ q*(L:ℝ) := mul_nonneg (hp.trans hpq) (by positivity)
        have hz := (Nat.floor_lt hqL).mp hj''
        have ht : 1 ≤ tilted 1 q v j := one_le_exp (by rw [one_mul]; exact mul_nonneg hv.le (sub_nonneg.mpr hz.le))
        exact ht.trans (le_add_of_nonneg_left (exp_pos _).le)
      · have hz : ((antisymmetric j).card : ℝ) ≤ p*L :=
          (Nat.cast_le.mpr (by omega : (antisymmetric j).card ≤ a)).trans
            (Nat.floor_le (mul_nonneg hp (by positivity)))
        have ht : 1 ≤ tilted (-1) p u j := one_le_exp (mul_nonneg_of_nonpos_of_nonpos
          (by linarith) (sub_nonpos.mpr hz))
        exact ht.trans (le_add_of_nonneg_right (exp_pos _).le)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => add_nonneg (exp_pos _).le (exp_pos _).le)

end VWZClique.RankSwap

open VWZClique VWZClique.RankSwap Filter Real

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀,
      ∃ (M : ℕ) (m : Fin M → Mask L) (c : Fin M → ℤ)
        (Λ : Finset (BasisLabel L)) (d : BasisLabel L → ℚ),
        (M : ℝ) ≤ ((2:ℝ)^L)^ε ∧ (Λ.card : ℝ) ≤ ((2:ℝ)^L)^(2-δ) ∧
        ∀ x y : PairBits L,
          (if x = y then (1 : ℚ) else 0) =
            (∑ j ∈ Λ, d j * basisEntry j x * basisEntry j y) +
            ∑ i, (c i : ℚ) * swapEntry (m i) x y := by
  intro ε hε
  obtain ⟨t, η, ht, hη, hη', hs⟩ := sparse_parameters ε hε
  let p := 1/4 - η
  let q := 1/4 + η
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hpq : p ≤ q := by dsimp [p,q]; linarith
  obtain ⟨u,hu,hu'⟩ := improving_tilt (-1) p (by dsimp [p]; linarith)
  obtain ⟨v,hv,hv'⟩ := improving_tilt 1 q (by dsimp [q]; linarith)
  obtain ⟨δ,hδ,hL⟩ := combine_tails (moment_pos _ _ _) (moment_pos _ _ _) hu' hv'
  obtain ⟨N,hN⟩ := eventually_atTop.1 hL
  refine ⟨δ,hδ,max N ⌈1/η⌉₊,?_⟩
  intro L hL
  let a := ⌊p*L⌋₊
  let b := ⌊q*L⌋₊
  let d := b-a
  have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_right hpq (by positivity))
  have hw : (d : ℝ) ≤ 3*η*L := by
    have hlarge : 1/η ≤ (L : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hL))
    have hlarge' := (div_le_iff₀ hη).mp hlarge
    have ha := Nat.lt_floor_add_one (p*L)
    have hb := Nat.floor_le (mul_nonneg (hp.trans hpq) (Nat.cast_nonneg L))
    change _ < (a : ℝ) + 1 at ha
    change (b : ℝ) ≤ _ at hb
    dsimp only [p,q] at ha hb
    rw [show (d : ℝ) = (b : ℝ) - a from Nat.cast_sub hab]
    nlinarith
  obtain ⟨m,c,r,heq⟩ := finite_window L a d
  refine ⟨Fintype.card (Terms L d),m,c,outside L a d,r,?_,?_,heq⟩
  · rw [RankSwap.pow_comm]
    calc
      _ ≤ (1+4*exp (-t))^L * exp (t*d) := sparse_bound L d t ht.le
      _ ≤ (1+4*exp (-t))^L * exp ((L:ℝ)*(3*t*η)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        calc t*d ≤ t*(3*η*L) := mul_le_mul_of_nonneg_left hw ht.le
             _ = _ := by ring
      _ = ((1+4*exp (-t))*exp (3*t*η))^L := by rw [exp_nat_mul, mul_pow]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hs.le L
  · rw [RankSwap.pow_comm]
    exact (both_tails L p q u v hp hpq hu hv).trans (hN L ((le_max_left _ _).trans hL))
