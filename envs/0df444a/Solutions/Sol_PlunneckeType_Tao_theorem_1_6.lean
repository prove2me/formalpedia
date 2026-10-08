-- Prove2me | solution 1 for PlunneckeType.Tao.theorem_1_6
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-08T01:56:02.069522+00:00
-- url     : https://prove2.me/submissions/0f278de0-f742-422e-b032-397380841de7

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me 5eeabb70-7692-4b85-b8cc-288bdc26d200.
-- Complete noncommutative Tao growth proof using proved Petridis, Ruzsa triangle and covering results.
import Mathlib

set_option autoImplicit false


-- BEGIN MODULE RatioMinimizer
section

open scoped Pointwise
open Finset
namespace PlunneckeType.Tao.Proof

lemma exists_ratio_minimizer {G : Type*} [Group G] [DecidableEq G]
    (A B : Finset G) (α : ℝ) (hA : A.Nonempty)
    (hAB : (#(A*B) : ℝ) ≤ α * #A) :
    ∃ X ⊆ A, X.Nonempty ∧
      (∀ Z ⊆ X, #(X*B) * #Z ≤ #(Z*B) * #X) ∧
      (#(X*B) : ℝ) ≤ α * #X := by
  classical
  let F : Finset (Finset G) := A.powerset.erase ∅
  have hAF : A ∈ F := by simp [F,hA.ne_empty]
  obtain ⟨X,hXF,hmin⟩ := F.exists_min_image
    (fun Z => (#(Z*B) : ℝ) / #Z) ⟨A,hAF⟩
  have hX : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hXF).1
  have hXA : X ⊆ A := Finset.mem_powerset.mp (Finset.mem_erase.mp hXF).2
  have hxpos : (0 : ℝ) < #X := by exact_mod_cast hX.card_pos
  have hapos : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  refine ⟨X,hXA,hX,?_,?_⟩
  · intro Z hZX
    by_cases hz : Z = ∅
    · simp [hz]
    · have hZF : Z ∈ F := by
        simp only [F,Finset.mem_erase,Finset.mem_powerset]
        exact ⟨hz,hZX.trans hXA⟩
      have hzpos : (0 : ℝ) < #Z := by
        exact_mod_cast (Finset.nonempty_iff_ne_empty.mpr hz).card_pos
      have hr := hmin Z hZF
      have hc := (div_le_div_iff₀ hxpos hzpos).mp hr
      exact_mod_cast hc
  · have hr := hmin A hAF
    have ha : (#(A*B) : ℝ) / #A ≤ α := (div_le_iff₀ hapos).mpr hAB
    exact (div_le_iff₀ hxpos).mp (hr.trans ha)

lemma exists_uniform_growth_subset {G : Type*} [Group G] [DecidableEq G]
    (A B : Finset G) (α : ℝ) (hA : A.Nonempty)
    (hAB : (#(A * B) : ℝ) ≤ α * #A) :
    ∃ S ⊆ A, S.Nonempty ∧ ∀ C : Finset G,
      (#(C * S * B) : ℝ) ≤ α * #(C * S) := by
  obtain ⟨S, hSA, hS, hmin, hSB⟩ := exists_ratio_minimizer A B α hA hAB
  refine ⟨S, hSA, hS, ?_⟩
  intro C
  have hspos : (0 : ℝ) < #S := by exact_mod_cast hS.card_pos
  have hpet : (#(C * S * B) : ℝ) * #S ≤ #(S * B) * #(C * S) := by
    exact_mod_cast Finset.pluennecke_petridis_inequality_mul C hmin
  have hbound := mul_le_mul_of_nonneg_right hSB (Nat.cast_nonneg (α := ℝ) #(C * S))
  nlinarith

end PlunneckeType.Tao.Proof
end
-- END MODULE RatioMinimizer

-- BEGIN MODULE ProductBounds
section
set_option autoImplicit false
open scoped Pointwise
open Finset
namespace PlunneckeType.Tao.Proof
variable {G : Type*} [Group G] [DecidableEq G]

lemma triangle_bound (Y X Z : Finset G) (hX : X.Nonempty) :
    (#(Y*Z):ℝ) ≤ (#(Y*X⁻¹):ℝ) * #(X*Z) / #X := by
  have hp : (0:ℝ) < #X := by exact_mod_cast hX.card_pos
  apply (le_div_iff₀ hp).mpr
  have h := Finset.ruzsa_triangle_inequality_mul_div_mul Y X Z
  rw [div_eq_mul_inv] at h
  have he : #(X*Y⁻¹) = #(Y*X⁻¹) := by
    rw [← card_inv (X*Y⁻¹), mul_inv_rev, inv_inv]
  rw [he] at h
  have hc : (#X:ℝ) * #(Y*Z) ≤ (#(Y*X⁻¹):ℝ) * #(X*Z) := by exact_mod_cast h
  nlinarith

lemma right_cover (S B : Finset G) (α : ℝ) (hS : S.Nonempty)
    (hSB : (#(S*B):ℝ) ≤ α * #S) :
    ∃ T ⊆ B, (#T:ℝ) ≤ α ∧ B ⊆ S⁻¹*S*T := by
  have hi : (#(B⁻¹*S⁻¹):ℝ) ≤ α * #S⁻¹ := by
    simpa only [← mul_inv_rev, card_inv] using hSB
  obtain ⟨F,hF,hcard,hcover⟩ := Finset.ruzsa_covering_mul hS.inv hi
  refine ⟨F⁻¹, ?_, ?_, ?_⟩
  · simpa only [inv_inv] using Finset.inv_subset_inv hF
  · simpa only [card_inv] using hcard
  · have hh := Finset.inv_subset_inv hcover
    simpa only [inv_inv, div_eq_mul_inv, mul_inv_rev, mul_assoc] using hh

lemma sandwich_card_le (A S T B : Finset G) (α β : ℝ) (hSA : S ⊆ A)
    (hTB : T ⊆ B) (hT : (#T:ℝ) ≤ α) (hβ : 0 ≤ β)
    (hAB : ∀ b ∈ B, (#(A*{b}*B):ℝ) ≤ β * #A) :
    (#(S*T*B):ℝ) ≤ α * β * #A := by
  classical
  have he : S*T*B = T.biUnion (fun b => S*{b}*B) := by
    ext z
    simp only [mem_mul, mem_biUnion, mem_singleton]
    constructor
    · rintro ⟨y,⟨s,hs,t,ht,rfl⟩,b,hb,rfl⟩
      exact ⟨t,ht,s*t,⟨s,hs,t,rfl,rfl⟩,b,hb,rfl⟩
    · rintro ⟨t,ht,y,⟨s,hs,t',htt,rfl⟩,b,hb,rfl⟩
      subst t'
      exact ⟨s*t,⟨s,hs,t,ht,rfl⟩,b,hb,rfl⟩
  calc
    (#(S*T*B):ℝ) = #(T.biUnion (fun b => S*{b}*B)) := by rw [he]
    _ ≤ ∑ b ∈ T, (#(S*{b}*B):ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ b ∈ T, β * #A := by
      apply Finset.sum_le_sum
      intro b hb
      have hs : S*{b}*B ⊆ A*{b}*B := by gcongr
      exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (hAB b (hTB hb))
    _ = (#T:ℝ) * (β * #A) := by simp [mul_comm]
    _ ≤ α * β * #A := by
      have hh := mul_le_mul_of_nonneg_right hT (mul_nonneg hβ (Nat.cast_nonneg #A))
      simpa only [mul_assoc] using hh
end PlunneckeType.Tao.Proof
end
-- END MODULE ProductBounds

-- BEGIN MODULE ConjugateBound
section

open scoped Pointwise
open Finset
namespace PlunneckeType.Tao.Proof
variable {G : Type*} [Group G] [DecidableEq G]

lemma conjugate_bound (A B : Finset G) (α : ℝ) (hB : B.Nonempty)
    (_hα : 0 ≤ α) (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hBAB : (#(B * A * B) : ℝ) ≤ α ^ 2 * #B) :
    (#(B * A⁻¹ * A * B⁻¹) : ℝ) ≤ α ^ 6 * #B := by
  have hbpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  have hfirst := triangle_bound (B * A) B⁻¹ B⁻¹ hB.inv
  have hinv : #(B⁻¹ * B⁻¹) = #(B * B) := by
    rw [← mul_inv_rev, card_inv]
  simp only [inv_inv, card_inv, hinv] at hfirst
  have hprod : (#(B * A * B) : ℝ) * #(B * B) ≤
      (α ^ 2 * #B) * (α * #B) :=
    mul_le_mul hBAB hBB (Nat.cast_nonneg _) (by positivity)
  have htriple : (#(B * A * B⁻¹) : ℝ) ≤ α ^ 3 * #B := by
    have hf := (le_div_iff₀ hbpos).mp hfirst
    nlinarith
  have hsecond := triangle_bound (B * A⁻¹) B (A * B⁻¹) hB
  have he : #(B * A⁻¹ * B⁻¹) = #(B * A * B⁻¹) := by
    rw [← card_inv (B * A⁻¹ * B⁻¹)]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  simp only [← mul_assoc, he] at hsecond
  have hs := (le_div_iff₀ hbpos).mp hsecond
  have hsquare : ((#(B * A * B⁻¹) : ℝ)) ^ 2 ≤ (α ^ 3 * #B) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) htriple 2
  nlinarith

lemma exists_conjugate_control (B : Finset G) (α : ℝ) (hB : B.Nonempty)
    (hα : 0 ≤ α) (hBB : (#(B * B) : ℝ) ≤ α * #B) :
    ∃ A ⊆ B, A.Nonempty ∧ (#(A * B) : ℝ) ≤ α * #A ∧
      (#(B * A⁻¹ * A * B⁻¹) : ℝ) ≤ α ^ 6 * #B := by
  obtain ⟨A, hAB, hA, hu⟩ := exists_uniform_growth_subset B B α hB hBB
  have hab : (#(A * B) : ℝ) ≤ α * #A := by simpa using hu 1
  have hba : (#(B * A) : ℝ) ≤ #(B * B) := by
    exact_mod_cast Finset.card_le_card (Finset.mul_subset_mul (Subset.refl B) hAB)
  have hbab : (#(B * A * B) : ℝ) ≤ α ^ 2 * #B := by
    have hh := (hu B).trans (mul_le_mul_of_nonneg_left hba hα)
    have hh' := mul_le_mul_of_nonneg_left hBB hα
    nlinarith
  exact ⟨A, hAB, hA, hab, conjugate_bound A B α hB hα hBB hbab⟩

end PlunneckeType.Tao.Proof
end
-- END MODULE ConjugateBound

-- BEGIN MODULE ParameterSigns
section

open scoped Pointwise
open Finset
namespace PlunneckeType.Tao.Proof

lemma parameter_nonneg {G : Type*} [Group G] [DecidableEq G]
    (B : Finset G) (α β : ℝ) (hB : B.Nonempty)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B) :
    0 ≤ α ∧ 0 ≤ β := by
  have hbpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  obtain ⟨b, hb⟩ := hB
  have hαmul : 0 ≤ α * #B := (Nat.cast_nonneg _).trans hBB
  have hβmul : 0 ≤ β * #B := (Nat.cast_nonneg _).trans (hBbB b hb)
  exact ⟨(mul_nonneg_iff_of_pos_right hbpos).mp hαmul,
    (mul_nonneg_iff_of_pos_right hbpos).mp hβmul⟩

end PlunneckeType.Tao.Proof
end
-- END MODULE ParameterSigns

-- BEGIN MODULE TaoControl
section
set_option autoImplicit false
open scoped Pointwise
open Finset
namespace PlunneckeType.Tao.Proof
variable {G : Type*} [Group G] [DecidableEq G]

lemma covered_product_bound (A B T Z : Finset G) (α : ℝ) (hB : B.Nonempty)
    (hcover : B ⊆ A⁻¹*A*T)
    (hD : (#(B*A⁻¹*A*B⁻¹):ℝ) ≤ α^6 * #B) :
    (#(B*B*Z):ℝ) ≤ α^6 * #(B*T*Z) := by
  have hb : (0:ℝ) < #B := by exact_mod_cast hB.card_pos
  have hsub : B*B*Z ⊆ (B*A⁻¹*A)*(T*Z) := by
    calc
      B*B*Z ⊆ B*(A⁻¹*A*T)*Z := by gcongr
      _ = (B*A⁻¹*A)*(T*Z) := by simp only [mul_assoc]
  have ht := triangle_bound (B*A⁻¹*A) B (T*Z) hB
  simp only [← mul_assoc] at ht
  have hh : (#(B*B*Z):ℝ) ≤ (#(B*A⁻¹*A*B⁻¹):ℝ) * #(B*T*Z) / #B :=
    (Nat.cast_le.mpr (card_le_card hsub)).trans (by simpa only [mul_assoc] using ht)
  apply (le_of_mul_le_mul_right · hb)
  have hmul := (le_div_iff₀ hb).mp hh
  have hm := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg #(B*T*Z))
  nlinarith

lemma sandwich_tail_bound (B T Z : Finset G) (α β : ℝ) (hB : B.Nonempty)
    (hBTB : (#(B*T*B):ℝ) ≤ α*β*#B) :
    (#(B*T*Z):ℝ) ≤ α*β*#(B⁻¹*Z) := by
  have hb : (0:ℝ) < #B := by exact_mod_cast hB.card_pos
  have ht := triangle_bound (B*T) B⁻¹ Z hB.inv
  simp only [inv_inv,card_inv] at ht
  have hm := mul_le_mul_of_nonneg_right hBTB (Nat.cast_nonneg #(B⁻¹*Z))
  have ht' := (le_div_iff₀ hb).mp ht
  apply (le_of_mul_le_mul_right · hb)
  nlinarith

lemma inverse_tail_bound (B Z : Finset G) (α : ℝ) (hB : B.Nonempty)
    (hBB : (#(B*B):ℝ) ≤ α*#B) :
    (#(B⁻¹*Z):ℝ) ≤ α*#(B*Z) := by
  have hb : (0:ℝ) < #B := by exact_mod_cast hB.card_pos
  have ht := triangle_bound B⁻¹ B Z hB
  have he : #(B⁻¹*B⁻¹) = #(B*B) := by rw [← mul_inv_rev,card_inv]
  rw [he] at ht
  have hm := mul_le_mul_of_nonneg_right hBB (Nat.cast_nonneg #(B*Z))
  have ht' := (le_div_iff₀ hb).mp ht
  apply (le_of_mul_le_mul_right · hb)
  nlinarith

lemma base_and_step (B : Finset G) (α β : ℝ) (hB : B.Nonempty)
    (hBB : (#(B*B):ℝ) ≤ α*#B)
    (hBbB : ∀ b ∈ B, (#(B*{b}*B):ℝ) ≤ β*#B) :
    (#(B*B*B):ℝ) ≤ α^7*β*#B ∧
      ∀ Z : Finset G, (#(B*B*Z):ℝ) ≤ α^8*β*#(B*Z) := by
  obtain ⟨hα,hβ⟩ := parameter_nonneg B α β hB hBB hBbB
  obtain ⟨A,_hAB,hA,hABgrowth,hD⟩ := exists_conjugate_control B α hB hα hBB
  obtain ⟨T,hTB,hT,hcover⟩ := right_cover A B α hA hABgrowth
  have hBTB := sandwich_card_le B B T B α β (Subset.refl B) hTB hT hβ hBbB
  constructor
  · calc
      (#(B*B*B):ℝ) ≤ α^6 * #(B*T*B) := covered_product_bound A B T B α hB hcover hD
      _ ≤ α^6 * (α*β*#B) := mul_le_mul_of_nonneg_left hBTB (by positivity)
      _ = α^7*β*#B := by ring
  · intro Z
    calc
      (#(B*B*Z):ℝ) ≤ α^6 * #(B*T*Z) := covered_product_bound A B T Z α hB hcover hD
      _ ≤ α^6 * (α*β*#(B⁻¹*Z)) := mul_le_mul_of_nonneg_left
        (sandwich_tail_bound B T Z α β hB hBTB) (by positivity)
      _ ≤ α^6 * (α*β*(α*#(B*Z))) := by
        gcongr
        exact inverse_tail_bound B Z α hB hBB
      _ = α^8*β*#(B*Z) := by ring
end PlunneckeType.Tao.Proof
end
-- END MODULE TaoControl

-- BEGIN MODULE PowerGrowth
section
set_option autoImplicit false
open scoped Pointwise
open Finset
namespace PlunneckeType.Tao.Proof
variable {G : Type*} [Group G] [DecidableEq G]

lemma power_growth_offset (B : Finset G) (α β : ℝ) (hB : B.Nonempty)
    (hBB : (#(B*B):ℝ) ≤ α*#B)
    (hBbB : ∀ b ∈ B, (#(B*{b}*B):ℝ) ≤ β*#B) :
    ∀ k : ℕ, (#(B^(k+3)):ℝ) ≤ α^(8*k+7)*β^(k+1)*#B := by
  obtain ⟨hα,hβ⟩ := parameter_nonneg B α β hB hBB hBbB
  obtain ⟨hbase,hstep⟩ := base_and_step B α β hB hBB hBbB
  intro k
  induction k with
  | zero => simpa [pow_succ,pow_two] using hbase
  | succ k ih =>
    have hs : (#(B^(k+1+3)):ℝ) ≤ α^8*β*#(B^(k+3)) := by
      have hh := hstep (B^(k+2))
      simpa only [mul_assoc,← pow_succ',Nat.add_assoc,Nat.reduceAdd] using hh
    calc
      (#(B^(k+1+3)):ℝ) ≤ α^8*β*#(B^(k+3)) := hs
      _ ≤ α^8*β*(α^(8*k+7)*β^(k+1)*#B) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg (by positivity) hβ)
      _ = α^(8*(k+1)+7)*β^(k+1+1)*#B := by
        rw [show 8*(k+1)+7 = (8*k+7)+8 by omega,pow_add,pow_succ]
        ring

lemma full_power_growth (B : Finset G) (α β : ℝ)
    (hBB : (#(B*B):ℝ) ≤ α*#B)
    (hBbB : ∀ b ∈ B, (#(B*{b}*B):ℝ) ≤ β*#B)
    (h : ℕ) (hh : 2 < h) :
    (#(B^h):ℝ) ≤ α^(8*h-17)*β^(h-2)*#B := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp [Finset.empty_pow (by omega : h ≠ 0)]
  · have hk := power_growth_offset B α β hB hBB hBbB (h-3)
    simpa only [show h-3+3=h by omega, show 8*(h-3)+7=8*h-17 by omega,
      show h-3+1=h-2 by omega] using hk
end PlunneckeType.Tao.Proof
end
-- END MODULE PowerGrowth

-- BEGIN MODULE FullGrowth
section
open scoped Pointwise
open Finset

namespace PlunneckeType.Tao

/-- Petridis, arXiv:1101.3507v3, p. 4, Theorem 1.6 (an explicit form of Tao's theorem). Let `B`
be a finite set in a (not necessarily commutative) group with `|BB| ≤ α|B|` and `|BbB| ≤ β|B|` for
all `b ∈ B`. Then for every `h > 2`, `|Bʰ| ≤ α^(8h−17) β^(h−2) |B|`. The natural-number exponents
`8h − 17` and `h − 2` are exact because `h ≥ 3`. -/
theorem theorem_1_6 {G : Type*} [Group G] [DecidableEq G] (B : Finset G) (α β : ℝ)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B)
    (h : ℕ) (hh : 2 < h) :
    (#(B ^ h) : ℝ) ≤ α ^ (8 * h - 17) * β ^ (h - 2) * #B := by
  exact Proof.full_power_growth B α β hBB hBbB h hh

end PlunneckeType.Tao

end
-- END MODULE FullGrowth

-- BEGIN MODULE PublicSolution
section
open scoped Pointwise
open Finset

theorem solution {G : Type*} [Group G] [DecidableEq G] (B : Finset G) (α β : ℝ)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B)
    (h : ℕ) (hh : 2 < h) :
    (#(B ^ h) : ℝ) ≤ α ^ (8 * h - 17) * β ^ (h - 2) * #B := by
  exact PlunneckeType.Tao.theorem_1_6 B α β hBB hBbB h hh


end
-- END MODULE PublicSolution

#print axioms PlunneckeType.Tao.theorem_1_6
#print axioms solution
