-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P09.vertex_maximalChain
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:13:53.440521+00:00
-- url     : https://prove2.me/submissions/d667e1cb-dbbb-4b73-89d3-f484eb7ee035

import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_tightSets_unionIntersection
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace X9Vertex

variable {α : Type} [Fintype α] [DecidableEq α]

private lemma vertex_kernel (f : Finset α → ℝ) (Q : α → ℝ)
    (hv : Q ∈ ({x : α → ℝ | ∀ S, f S ≤ ∑ a ∈ S, x a}).extremePoints ℝ)
    (v : α → ℝ) (hz : ∀ S, (∑ a ∈ S, Q a) = f S → (∑ a ∈ S, v a) = 0) :
    v = 0 := by
  classical
  have hQ := hv.1
  have he : ∀ S : Finset α, ∃ e : ℝ, 0 < e ∧
      e * |∑ a ∈ S, v a| ≤ (∑ a ∈ S, Q a) - f S := by
    intro S
    by_cases ht : (∑ a ∈ S, Q a) = f S
    · refine ⟨1, by norm_num, ?_⟩
      simp [hz S ht, ht]
    · obtain ⟨e, he, hb⟩ := exists_pos_mul_lt (sub_pos.mpr (lt_of_le_of_ne (hQ S) (Ne.symm ht)))
        |∑ a ∈ S, v a|
      exact ⟨e, he, by nlinarith⟩
  choose e he hb using he
  obtain ⟨S₀, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Finset α)) e
    (by simp)
  let δ := e S₀
  have hd : 0 < δ := he S₀
  have hbound (S : Finset α) : δ * |∑ a ∈ S, v a| ≤ (∑ a ∈ S, Q a) - f S :=
    (mul_le_mul_of_nonneg_right (hmin S (Finset.mem_univ S)) (abs_nonneg _)).trans (hb S)
  have hplus : Q + δ • v ∈ {x : α → ℝ | ∀ S, f S ≤ ∑ a ∈ S, x a} := by
    intro S
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have hh := hbound S
    have ha := neg_abs_le (∑ a ∈ S, v a)
    have hm := mul_le_mul_of_nonneg_left ha hd.le
    nlinarith
  have hminus : Q - δ • v ∈ {x : α → ℝ | ∀ S, f S ≤ ∑ a ∈ S, x a} := by
    intro S
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    have hh := hbound S
    have ha := le_abs_self (∑ a ∈ S, v a)
    have hm := mul_le_mul_of_nonneg_left ha hd.le
    nlinarith
  have h := hv.2 hplus hminus (mem_openSegment_add_sub (𝕜 := ℝ) Q (δ • v))
  funext a
  have ha := congrFun h a
  change Q a + δ * v a = Q a at ha
  have : δ * v a = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left hd.ne'

private lemma vertex_cover (f : Finset α → ℝ) (Q : α → ℝ)
    (hv : Q ∈ ({x : α → ℝ | ∀ S, f S ≤ ∑ a ∈ S, x a}).extremePoints ℝ) :
    ∀ a, ∃ S, (∑ b ∈ S, Q b) = f S ∧ a ∈ S := by
  classical
  intro a
  by_contra hn
  push Not at hn
  have h := vertex_kernel f Q hv (fun b => if b = a then 1 else 0) (by
    intro S ht
    have ha : a ∉ S := fun ha => hn S ht ha
    simp [Finset.sum_ite_eq', ha])
  have := congrFun h a
  simp at this

private lemma vertex_separates (f : Finset α → ℝ) (Q : α → ℝ)
    (hv : Q ∈ ({x : α → ℝ | ∀ S, f S ≤ ∑ a ∈ S, x a}).extremePoints ℝ) :
    ∀ a b, (∀ S, (∑ c ∈ S, Q c) = f S → (a ∈ S ↔ b ∈ S)) → a = b := by
  classical
  intro a b hab
  by_contra hne
  have h := vertex_kernel f Q hv (fun c => (if c = a then 1 else 0) -
      (if c = b then 1 else 0)) (by
    intro S ht
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq']
    by_cases ha : a ∈ S
    · simp [ha, (hab S ht).mp ha]
    · have hb : b ∉ S := fun hb => ha ((hab S ht).mpr hb)
      simp [ha, hb])
  have := congrFun h a
  simp [hne] at this

private lemma family_top (F : Finset α → Prop) (h0 : F ∅)
    (hu : ∀ S T, F S → F T → F (S ∪ T))
    (hc : ∀ a, ∃ S, F S ∧ a ∈ S) : F Finset.univ := by
  classical
  have hf (c : Finset (Finset α)) : (∀ S ∈ c, F S) → F (c.biUnion id) := by
    induction c using Finset.induction_on with
    | empty => simp [h0]
    | @insert S c hn ih =>
      intro h
      simpa using hu S (c.biUnion id) (h S (Finset.mem_insert_self _ _))
        (ih (fun T hT => h T (Finset.mem_insert_of_mem hT)))
  let c := Finset.univ.filter F
  have hall : c.biUnion id = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    obtain ⟨S, hS, ha⟩ := hc a
    exact Finset.mem_biUnion.mpr ⟨S, by simp [c, hS], ha⟩
  rw [← hall]
  exact hf c (by simp [c])

private lemma family_predecessor (F : Finset α → Prop) (h0 : F ∅)
    (hu : ∀ S T, F S → F T → F (S ∪ T))
    (hi : ∀ S T, F S → F T → F (S ∩ T))
    (hsep : ∀ a b, (∀ S, F S → (a ∈ S ↔ b ∈ S)) → a = b)
    (S : Finset α) (hS : F S) (hne : S.Nonempty) :
    ∃ a ∈ S, F (S.erase a) := by
  classical
  let c := Finset.univ.filter (fun T : Finset α => F T ∧ T ⊂ S)
  have hc : c.Nonempty := ⟨∅, by simp [c, h0, hne]⟩
  obtain ⟨T, hTc, hmax⟩ := Finset.exists_max_image c Finset.card hc
  obtain ⟨hT, hTS⟩ := (Finset.mem_filter.mp hTc).2
  obtain ⟨a, haS, haT⟩ := Finset.exists_of_ssubset hTS
  have same (b : α) (hbS : b ∈ S) (hbT : b ∉ T) : a = b := by
    apply hsep
    intro L hL
    have imp (x y : α) (hxS : x ∈ S) (hxT : x ∉ T) (hyS : y ∈ S) (hyT : y ∉ T)
        (hxL : x ∈ L) : y ∈ L := by
      by_contra hyL
      let U := T ∪ (L ∩ S)
      have hU : F U := hu T (L ∩ S) hT (hi L S hL hS)
      have hUS : U ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro z hz
          rcases Finset.mem_union.mp hz with hz | hz
          · exact hTS.1 hz
          · exact (Finset.mem_inter.mp hz).2
        · intro heq
          have : y ∈ U := heq.symm ▸ hyS
          simp [U, hyT, hyL] at this
      have hTU : T ⊂ U := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
        intro heq
        have : x ∈ U := by simp [U, hxL, hxS]
        exact hxT (heq.symm ▸ this)
      have hcard := hmax U (by simp [c, hU, hUS])
      exact (not_lt_of_ge hcard) (Finset.card_lt_card hTU)
    exact ⟨imp a b haS haT hbS hbT, imp b a hbS hbT haS haT⟩
  refine ⟨a, haS, ?_⟩
  have heq : S.erase a = T := by
    ext b
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨hba, hbS⟩
      by_contra hbT
      exact hba (same b hbS hbT).symm
    · intro hbT
      exact ⟨fun hba => haT (hba ▸ hbT), hTS.1 hbT⟩
  rwa [heq]

private lemma family_chain (F : Finset α → Prop) (h0 : F ∅)
    (hu : ∀ S T, F S → F T → F (S ∪ T))
    (hi : ∀ S T, F S → F T → F (S ∩ T))
    (hsep : ∀ a b, (∀ S, F S → (a ∈ S ↔ b ∈ S)) → a = b)
    (S : Finset α) (hS : F S) :
    ∃ K : ℕ → Finset α, K 0 = ∅ ∧ K S.card = S ∧
      (∀ i, i ≤ S.card → F (K i)) ∧ (∀ i, i < S.card → K i ⊂ K (i+1)) ∧
      (∀ x y : α → ℝ, (∀ i, i ≤ S.card → (∑ a ∈ K i, x a) = ∑ a ∈ K i, y a) →
        ∀ a ∈ S, x a = y a) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases he : S = ∅
    · subst S
      refine ⟨fun _ => ∅, rfl, rfl, ?_, ?_, ?_⟩
      · exact fun _ _ => h0
      · simp
      · simp
    · have hne := Finset.nonempty_iff_ne_empty.mpr he
      obtain ⟨a, ha, hT⟩ := family_predecessor F h0 hu hi hsep S hS hne
      obtain ⟨L, hL0, hLast, hLF, hLstrict, hLunique⟩ :=
        ih (S.erase a) (Finset.erase_ssubset ha) hT
      let n := (S.erase a).card
      have hn : S.card = n + 1 := by
        dsimp [n]
        exact (Finset.card_erase_add_one ha).symm
      let K : ℕ → Finset α := fun i => if i ≤ n then L i else S
      have hK0 : K 0 = ∅ := by simpa [K] using hL0
      have hKn : K n = S.erase a := by simpa [K, n] using hLast
      have hKlast : K S.card = S := by simp [K, hn]
      refine ⟨K, hK0, hKlast, ?_, ?_, ?_⟩
      · intro i hbi
        by_cases hi : i ≤ n
        · simpa [K, hi] using hLF i hi
        · simp only [K, if_neg hi]
          exact hS
      · intro i hbi
        by_cases hi : i < n
        · simpa [K, Nat.le_of_lt hi, Nat.succ_le_iff.mpr hi] using hLstrict i hi
        · have hei : i = n := by omega
          subst i
          have hstep : K (n+1) = S := by simp [K]
          rw [hKn, hstep]
          exact Finset.erase_ssubset ha
      · intro x y heq b hb
        have heqL : ∀ i, i ≤ n → (∑ c ∈ L i, x c) = ∑ c ∈ L i, y c := by
          intro i hi
          simpa [K, hi] using heq i (by omega)
        have hprev := hLunique x y heqL
        by_cases hba : b = a
        · subst b
          have ht : (∑ c ∈ S.erase a, x c) = ∑ c ∈ S.erase a, y c :=
            Finset.sum_congr rfl hprev
          have hs : (∑ c ∈ S, x c) = ∑ c ∈ S, y c := by
            simpa [hKlast] using heq S.card le_rfl
          have hx := Finset.sum_erase_add S x ha
          have hy := Finset.sum_erase_add S y ha
          linarith
        · exact hprev b (Finset.mem_erase.mpr ⟨hba, hb⟩)

end X9Vertex

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P09
open QAlgorithms.Papers.Independent.Claimed50.P33
open scoped Matrix ComplexConjugate ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq

section Compression
variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)] [hD : ∀ i, Nonempty (D i)]
variable {R : Type} [Fintype R] [hR : Nonempty R]
variable (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1)
include hphi hD hR

theorem solution (hm : 0 < m) (Q : Fin m → ℝ)
    (hvertex : Q ∈ (entropyPolyhedron (pureDensity phi)).extremePoints ℝ) :
    ∃ K : Fin (m+1) → Finset (Fin m), IsMaximalChain K ∧
      {x | chainEquations (pureDensity phi) K x} = {Q} := by
  classical
  let f := entropyThreshold (pureDensity phi)
  let F : Finset (Fin m) → Prop := fun S => S = ∅ ∨ (∑ a ∈ S, Q a) = f S
  have h0 : F ∅ := Or.inl rfl
  have hclosure (S T : Finset (Fin m)) (hS : F S) (hT : F T) :
      F (S ∪ T) ∧ F (S ∩ T) := by
    rcases hS with rfl | hS
    · simpa [F] using And.intro hT h0
    rcases hT with rfl | hT
    · simpa [F] using And.intro (Or.inr hS : F S) h0
    obtain ⟨hu, hi⟩ := tightSets_unionIntersection phi hphi hm Q hvertex.1 S T hS hT
    exact ⟨Or.inr hu, Or.inr hi⟩
  have hu := fun S T hS hT => (hclosure S T hS hT).1
  have hi := fun S T hS hT => (hclosure S T hS hT).2
  have hcover : ∀ a, ∃ S, F S ∧ a ∈ S := by
    intro a
    obtain ⟨S, hS, ha⟩ := X9Vertex.vertex_cover f Q hvertex a
    exact ⟨S, Or.inr hS, ha⟩
  have hsep : ∀ a b, (∀ S, F S → (a ∈ S ↔ b ∈ S)) → a = b := by
    intro a b hab
    exact X9Vertex.vertex_separates f Q hvertex a b (fun S hS => hab S (Or.inr hS))
  have htop := X9Vertex.family_top F h0 hu hcover
  obtain ⟨L, hL0, hLast, hLF, hLstrict, hLunique⟩ :=
    X9Vertex.family_chain F h0 hu hi hsep Finset.univ htop
  simp only [Finset.card_univ, Fintype.card_fin] at hLast hLF hLstrict hLunique
  let K : Fin (m+1) → Finset (Fin m) := fun i => L i.val
  have hK : IsMaximalChain K := by
    exact ⟨hL0, hLast, fun j => hLstrict j.val j.isLt⟩
  have hQchain : chainEquations (pureDensity phi) K Q := by
    intro j
    have hF := hLF (j.val+1) (by omega)
    rcases hF with he | ht
    · have hh := hLstrict j.val j.isLt
      rw [he] at hh
      exact False.elim (Finset.not_ssubset_empty _ hh)
    · exact ht
  refine ⟨K, hK, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    funext a
    apply hLunique x Q ?_ a (Finset.mem_univ a)
    intro i hi
    by_cases hz : i = 0
    · subst i
      simp [hL0]
    · let j : Fin m := ⟨i-1, by omega⟩
      have hj : j.val + 1 = i := by dsimp [j]; omega
      have he := (hx j).trans (hQchain j).symm
      change (∑ b ∈ L (j.val+1), x b) = ∑ b ∈ L (j.val+1), Q b at he
      rwa [hj] at he
  · rintro rfl
    exact hQchain
end Compression
