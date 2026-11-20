-- Prove2me | solution 1 for QuantumSixJ.network_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @igor.kh
-- created : 2026-11-13T09:29:12.803365+00:00
-- url     : https://prove2.me/submissions/b6d2d0ba-29e2-40c6-9daf-605f04a51fbb

import Definitions.Def_QuantumSixJRecurrences
import Theorems.Thm_QuantumSixJ_scalar_foundations
import Theorems.Thm_QuantumSixJ_Network_four_valent_bases
import Theorems.Thm_QuantumSixJ_Network_rung_eigenvalue
import Theorems.Thm_QuantumSixJ_Network_matrix_entries

open CategoryTheory MonoidalCategory
universe v u
noncomputable section
open QuantumSixJ
open scoped BigOperators QuantumSixJ Classical

private def q_ne_zero := QuantumSixJ.scalar_foundations.1
private def q_denominator_ne_zero := QuantumSixJ.scalar_foundations.2.1
private def qInt_ne_zero := QuantumSixJ.scalar_foundations.2.2.1
private def qFactorial_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.1
private def delta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.1
private def theta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.1
private def h_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.1
private def x_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.1
private def tet_summand_support_bounds := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.1
private def tet_appendix_bounds_within_coarse := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.2.1

namespace QuantumSixJ
def diagonalEntry (a b c d j : ℤ) : Scalar :=
  if hAdmissible a b c d j ∧ j ≠ 0 then
    -h a b c d j * ⟬2⟭ * Λ a j d * Λ b j c / (⟬j⟭ * ⟬j + 2⟭)
  else 0

def Lp2 (a b c d j : ℤ) : Scalar :=
  if hAdmissible a b c d j ∧ hAdmissible a b c d (j + 2) then
    h a b c d (j + 2) * ⟬(a + d - j) / 2⟭ * ⟬(b + c - j) / 2⟭
  else 0

def Lm2 (a b c d j : ℤ) : Scalar :=
  if hAdmissible a b c d j ∧ hAdmissible a b c d (j - 2) then
    h a b c d j * ⟬(a + d - (j - 2)) / 2⟭ * ⟬(b + c - (j - 2)) / 2⟭
  else 0

end QuantumSixJ
private lemma matrix_diag (a b c d j : ℤ) :
    L a b c d j j = diagonalEntry a b c d j := by
  simp [L, diagonalEntry]

private lemma matrix_upper (a b c d j : ℤ) :
    L a b c d j (j + 2) = Lp2 a b c d j := by
  have hn : j ≠ j + 2 := by omega
  unfold L
  rw [if_neg hn, if_pos (show j + 2 = j + 2 ∨ j = j + 2 + 2 from Or.inl rfl)]
  dsimp only
  rw [min_eq_left (show j ≤ j + 2 by omega), max_eq_right (show j ≤ j + 2 by omega)]
  rfl

private lemma matrix_lower (a b c d j : ℤ) :
    L a b c d j (j - 2) = Lm2 a b c d j := by
  have hn : j ≠ j - 2 := by omega
  have he : j = j - 2 + 2 := by omega
  unfold L
  rw [if_neg hn, if_pos (Or.inr he : j - 2 = j + 2 ∨ j = j - 2 + 2)]
  dsimp only
  rw [min_eq_right (show j - 2 ≤ j by omega), max_eq_left (show j - 2 ≤ j by omega)]
  by_cases hj : hAdmissible a b c d j <;>
    by_cases hm : hAdmissible a b c d (j - 2) <;>
    simp only [Lm2, hj, hm, and_self, true_and, false_and,
      and_false, and_true, if_true, if_false] <;> rfl


namespace QuantumSixJ.Network.Vertex
def overlapTet {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    {S : SuQ2Data C} (W : Vertex S) (a b c d : ℕ) (j l : ℤ) : 𝟙_ C ⟶ 𝟙_ C :=
  if 0 ≤ j ∧ 0 ≤ l then W.X a b c d l.toNat ≫ W.Hcov a b c d j.toNat else 0
end QuantumSixJ.Network.Vertex
namespace QuantumSixJ.Network

private lemma unit_scalar_injective_rec {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) :
    Function.Injective (fun r : K => r • 𝟙 (𝟙_ C)) := by
  intro r s hrs
  have hrs0 : r • 𝟙 (S.V 0) = s • 𝟙 (S.V 0) := by
    have h := congrArg (fun f : 𝟙_ C ⟶ 𝟙_ C => S.unitIso.hom ≫ f ≫ S.unitIso.inv) hrs
    simpa [smul_smul] using h
  have hd : (0 : S.V 0 ⟶ S.V 0) = (r - s) • 𝟙 (S.V 0) := by
    rw [sub_smul, hrs0, sub_self]
  have hz : (0 : S.V 0 ⟶ S.V 0) = (0 : K) • 𝟙 (S.V 0) := by simp
  exact sub_eq_zero.mp ((hS.simple 0 0).unique hd hz)

private lemma unit_scalar_exists_rec {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) (f : 𝟙_ C ⟶ 𝟙_ C) :
    ∃ r : K, f = r • 𝟙 (𝟙_ C) := by
  obtain ⟨r, hr, _⟩ := hS.simple 0 (S.unitIso.hom ≫ f ≫ S.unitIso.inv)
  refine ⟨r, ?_⟩
  have h := congrArg (fun g : S.V 0 ⟶ S.V 0 => S.unitIso.inv ≫ g ≫ S.unitIso.hom) hr
  simpa [Category.assoc, smul_smul] using h

private lemma rec_core_aux {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b c d j l N : ℕ)
    (t m : ℕ → K) (hn : ℕ → Scalar) (lam : Scalar)
    (hX : W.X a b c d l =
      ∑ n ∈ Finset.range N, (t n / ι (hn n)) • W.H a b c d n)
    (hE : W.X a b c d l ≫ W.Kop a b c d = ι lam • W.X a b c d l)
    (ht : ∀ n : ℕ, W.X a b c d l ≫ W.Hcov a b c d n = t n • 𝟙 (𝟙_ C))
    (hM : ∀ n : ℕ, W.H a b c d n ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
      m n • 𝟙 (𝟙_ C)) :
    (∑ n ∈ Finset.range N, ((t n / ι (hn n)) * m n) • 𝟙 (𝟙_ C)) -
      (ι lam * t j) • 𝟙 (𝟙_ C) = 0 := by
  have hc : W.X a b c d l ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
      (ι lam * t j) • 𝟙 (𝟙_ C) := by
    calc
      W.X a b c d l ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
          (ι lam • W.X a b c d l) ≫ W.Hcov a b c d j := by
        simpa only [Category.assoc] using congrArg
          (fun f : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d =>
            f ≫ W.Hcov a b c d j) hE
      _ = ι lam • (t j • 𝟙 (𝟙_ C)) := by simp [ht j]
      _ = (ι lam * t j) • 𝟙 (𝟙_ C) := by rw [smul_smul]
  have hc' : (∑ n ∈ Finset.range N, (t n / ι (hn n)) • W.H a b c d n) ≫
      W.Kop a b c d ≫ W.Hcov a b c d j = (ι lam * t j) • 𝟙 (𝟙_ C) := by
    rw [← hX]
    exact hc
  have hsum : (∑ n ∈ Finset.range N, (t n / ι (hn n)) • W.H a b c d n) ≫
      W.Kop a b c d ≫ W.Hcov a b c d j =
        ∑ n ∈ Finset.range N, ((t n / ι (hn n)) * m n) • 𝟙 (𝟙_ C) := by
    rw [Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro n hn
    simp [hM n, smul_smul]
  have hc'' : (∑ n ∈ Finset.range N, ((t n / ι (hn n)) * m n) • 𝟙 (𝟙_ C)) =
      (ι lam * t j) • 𝟙 (𝟙_ C) := by
    rw [← hsum]
    exact hc'
  exact sub_eq_zero.mpr hc''

private lemma rec_sparse_aux (N j : ℕ) (r m d u : K) (v : ℕ → K) (hj : j < N)
    (M : ℕ → K)
    (hM : ∀ n : ℕ, M n =
      if n = j then d else if n = j + 2 then u else if j = n + 2 then r else 0) :
    (∑ n ∈ Finset.range N, v n * M n) =
      (if 2 ≤ j then v (j - 2) * r else 0) + v j * d +
        if j + 2 < N then v (j + 2) * u else 0 := by
  classical
  have hterm (n : ℕ) : v n * M n =
      (if n = j then v n * d else 0) +
        (if n = j + 2 then v n * u else 0) +
          if j = n + 2 then v n * r else 0 := by
    rw [hM n]
    clear hM
    split_ifs <;> (try {exfalso; omega}) <;>
      simp only [zero_add, add_zero, mul_zero, zero_mul] <;> ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  by_cases hl : 2 ≤ j
  · have hlmem : j - 2 ∈ Finset.range N := by simp only [Finset.mem_range]; omega
    have hidx : ∀ n : ℕ, (j = n + 2) ↔ n = j - 2 := by intro n; omega
    by_cases hu : j + 2 < N
    · have hjmem : j ∈ Finset.range N := Finset.mem_range.mpr hj
      have humem : j + 2 ∈ Finset.range N := Finset.mem_range.mpr hu
      simp [hl, hu, hjmem, humem, hlmem, hidx] <;> ring
    · have hnumem : j + 2 ∉ Finset.range N := by simpa using hu
      have hjmem : j ∈ Finset.range N := Finset.mem_range.mpr hj
      simp [hl, hu, hjmem, hnumem, hlmem, hidx] <;> ring
  · have hidx : ∀ n : ℕ, j ≠ n + 2 := by intro n; omega
    by_cases hu : j + 2 < N
    · have hjmem : j ∈ Finset.range N := Finset.mem_range.mpr hj
      have humem : j + 2 ∈ Finset.range N := Finset.mem_range.mpr hu
      simp [hl, hu, hjmem, humem, hidx] <;> ring
    · have hnumem : j + 2 ∉ Finset.range N := by simpa using hu
      have hjmem : j ∈ Finset.range N := Finset.mem_range.mpr hj
      simp [hl, hu, hjmem, hnumem, hidx] <;> ring

private lemma rec_hom_to_tensor_zero {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) (a b l : ℕ)
    (hna : ¬ Admissible (a : ℤ) b l) (f : S.V l ⟶ S.V a ⊗ S.V b) : f = 0 := by
  classical
  obtain ⟨i, p, _, hfusion⟩ := hS.fusion a b
  calc
    f = f ≫ 𝟙 (S.V a ⊗ S.V b) := by simp
    _ = f ≫ ∑ c ∈ fusionRange a b, p c ≫ i c := by rw [hfusion]
    _ = ∑ c ∈ fusionRange a b, f ≫ (p c ≫ i c) := by rw [Preadditive.comp_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      rcases Finset.mem_filter.mp hc with ⟨_, hcAdm⟩
      have hne : l ≠ c := by
        intro hlc
        subst c
        exact hna hcAdm
      rw [← Category.assoc]
      simp [hS.disjoint l c hne (f ≫ p c)]

private lemma rec_X_zero_left {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (a b c d l : ℕ)
    (hna : ¬ Admissible (a : ℤ) b l) : W.X a b c d l = 0 := by
  have hs : W.split l a b = 0 := rec_hom_to_tensor_zero S hS a b l hna _
  simp [Vertex.X, monoidalComp, hs]

private lemma rec_X_zero_right {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (a b c d l : ℕ)
    (hnc : ¬ Admissible (c : ℤ) d l) : W.X a b c d l = 0 := by
  have hs : W.split l c d = 0 := rec_hom_to_tensor_zero S hS c d l hnc _
  simp [Vertex.X, monoidalComp, hs]

private lemma rec_X_zero {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (a b c d l : ℕ)
    (hn : ¬ vAdmissible (a : ℤ) b c d l) : W.X a b c d l = 0 := by
  by_cases hab : Admissible (a : ℤ) b l
  · apply rec_X_zero_right S W hS
    intro hcd
    exact hn ⟨hab, hcd⟩
  · exact rec_X_zero_left S W hS a b c d l hab

private lemma rec_overlapTet_zero {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (a b c d : ℕ)
    (j : ℤ) (l : ℕ) (hn : ¬ vAdmissible (a : ℤ) b c d l) :
    W.overlapTet a b c d j l = 0 := by
  by_cases hj : 0 ≤ j
  · lift j to ℕ using hj
    simp [Vertex.overlapTet, rec_X_zero S W hS a b c d l hn]
  · simp [Vertex.overlapTet, hj]

private lemma rec_overlapTet_zero_int {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (a b c d : ℕ)
    (j l : ℤ) (hn : ¬ vAdmissible (a : ℤ) b c d l) :
    W.overlapTet a b c d j l = 0 := by
  by_cases hl : 0 ≤ l
  · lift l to ℕ using hl
    exact rec_overlapTet_zero S W hS a b c d j l hn
  · simp [Vertex.overlapTet, hl]

end QuantumSixJ.Network

open QuantumSixJ.Network

private lemma overlap_eq {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W)
    (a b c d : ℕ) (j l : ℤ) : W.overlapTet a b c d j l = W.tet a b c d j l := by
  by_cases hj : 0 ≤ j
  · by_cases hl : 0 ≤ l
    · lift j to ℕ using hj
      lift l to ℕ using hl
      simpa only [Vertex.overlapTet, Nat.cast_nonneg, and_self, if_true,
        Int.toNat_natCast] using
        (four_valent_bases S W hS hW a b c d).2.2.2.2.2.2.1 j l
    · simp [Vertex.overlapTet, Vertex.tet, hl]
  · simp [Vertex.overlapTet, Vertex.tet, hj]

private theorem input_expansion {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C] :
  ∀ (S : SuQ2Data C) (W : Vertex S), SuQ2Axioms S → VertexNormalized W →
    ∀ (a b c d l : ℕ) (s : ℕ → K),
      (∀ j : ℕ, W.overlapTet a b c d j l = s j • 𝟙 (𝟙_ C)) →
      W.X a b c d l =
        ∑ j ∈ Finset.range (b + c + 1), (s j / ι (h a b c d j)) • W.H a b c d j
 := by
  intro S W hS hW a b c d l s hs
  obtain ⟨t, ht, he⟩ := (four_valent_bases S W hS hW a b c d).2.2.1 (W.X a b c d l)
  have hts : t = s := by
    funext j
    apply unit_scalar_injective_rec S hS
    exact (ht j).symm.trans (by simpa [Vertex.overlapTet] using hs j)
  simpa only [hts] using he

private theorem input_eigenvector {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C] :
  ∀ (S : SuQ2Data C) (W : Vertex S), SuQ2Axioms S → VertexNormalized W → TetSeed W →
    ∀ a b c d l : ℕ, vAdmissible a b c d l →
      W.X a b c d l ≫ W.Kop a b c d = ι (Λ a b l) • W.X a b c d l
 := by
  intro S W hS hW hSeed a b c d l _
  exact (rung_eigenvalue S W hS hW hSeed).2.2 a b c d l

private theorem input_matrix {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C] :
  ∀ (S : SuQ2Data C) (W : Vertex S), SuQ2Axioms S → VertexNormalized W → TetSeed W →
    ∀ a b c d j : ℕ,
      W.H a b c d j ≫ W.Kop a b c d ≫ W.Hcov a b c d j = ι (diagonalEntry a b c d j) • 𝟙 (𝟙_ C) ∧
      W.H a b c d (j + 2) ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
        ι (Lp2 a b c d j) • 𝟙 (𝟙_ C) ∧
      W.H a b c d j ≫ W.Kop a b c d ≫ W.Hcov a b c d (j + 2) =
        ι (Lm2 a b c d (j + 2)) • 𝟙 (𝟙_ C) ∧
      ∀ j' : ℕ, j' ≠ j → j' ≠ j + 2 → j ≠ j' + 2 →
        W.H a b c d j' ≫ W.Kop a b c d ≫ W.Hcov a b c d j = 0
 := by
  intro S W hS hW hSeed a b c d j
  have hm := (matrix_entries S W hS hW hSeed).2.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [matrix_diag] using hm a b c d j j
  · simpa only [Nat.cast_add, Nat.cast_ofNat, matrix_upper] using hm a b c d j (j + 2)
  · have hh := matrix_lower (a : ℤ) b c d ((j + 2 : ℕ) : ℤ)
    rw [show ((j + 2 : ℕ) : ℤ) - 2 = (j : ℤ) by omega] at hh
    simp only [Nat.cast_add, Nat.cast_ofNat] at hh
    simpa only [hh, Nat.cast_add, Nat.cast_ofNat] using hm a b c d (j + 2) j
  · intro k hk0 hkp hkm
    have h0 : (k : ℤ) ≠ j := by omega
    have hp : (k : ℤ) ≠ (j : ℤ) + 2 := by omega
    have hm' : (k : ℤ) ≠ (j : ℤ) - 2 := by omega
    rw [hm a b c d j k, QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.2.2.2.1 a b c d j k h0 hm' hp]
    simp
private theorem overlap_recurrence {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C] :
    ∀ (S : SuQ2Data C) (W : Vertex S), SuQ2Axioms S → VertexNormalized W → TetSeed W →
      ∀ (a b c d : ℕ) (j l : ℤ),
        (ι (Lm2 a b c d j) / ι (h a b c d (j - 2))) • W.overlapTet a b c d (j - 2) l +
        (ι (diagonalEntry a b c d j - Λ a b l * h a b c d j) / ι (h a b c d j)) • W.overlapTet a b c d j l +
        (ι (Lp2 a b c d j) / ι (h a b c d (j + 2))) • W.overlapTet a b c d (j + 2) l = 0 := by
  classical
  intro S W hS hW hSeed a b c d j l
  by_cases hj : hAdmissible a b c d j
  · by_cases hv : vAdmissible a b c d l
    · have hj0 : 0 ≤ j := hj.1.2.2.1
      have hl : 0 ≤ l := hv.1.2.2.1
      lift j to ℕ using hj0
      lift l to ℕ using hl
      choose t ht using fun k : ℤ => unit_scalar_exists_rec S hS
        (W.overlapTet a b c d k (l : ℤ))
      have ht_nat (n : ℕ) : W.overlapTet a b c d n l = t n • 𝟙 (𝟙_ C) := by
        simpa using ht (n : ℤ)
      have hhn : ι (h (a : ℤ) b c d j) ≠ 0 := by
        apply (map_ne_zero_iff _ _).2 (h_ne_zero (a : ℤ) b c d j hj)
        unfold ι
        apply RatFunc.map_injective
        · exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
            (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective)
        · exact Polynomial.map_injective _ (algebraMap ℚ ℂ).injective
      have hmid :
          (ι (diagonalEntry (a : ℤ) b c d j - Λ (a : ℤ) b l * h (a : ℤ) b c d j) /
            ι (h (a : ℤ) b c d j)) * t j =
          t j / ι (h (a : ℤ) b c d j) * ι (diagonalEntry (a : ℤ) b c d j) -
            ι (Λ (a : ℤ) b l) * t j := by
        rw [map_sub, map_mul]
        field_simp [hhn]
        <;> ring
      have hX : W.X a b c d l =
          ∑ n ∈ Finset.range (b + c + 1),
            (t n / ι (h (a : ℤ) b c d n)) • W.H a b c d n :=
        input_expansion S W hS hW a b c d l (fun n => t n) (fun n => ht_nat n)
      have hE := input_eigenvector S W hS hW hSeed a b c d l hv
      let m : ℕ → K := fun n =>
        if n = j then ι (diagonalEntry (a : ℤ) b c d j) else
          if n = j + 2 then ι (Lp2 (a : ℤ) b c d j) else
            if j = n + 2 then ι (Lm2 (a : ℤ) b c d j) else 0
      have hmatn (n : ℕ) : W.H a b c d n ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
          m n • 𝟙 (𝟙_ C) := by
        by_cases hnj : n = j
        · subst n
          simpa [m] using (input_matrix S W hS hW hSeed a b c d j).1
        · by_cases hnu : n = j + 2
          · subst n
            simpa [m, hnj] using (input_matrix S W hS hW hSeed a b c d j).2.1
          · by_cases hnl : j = n + 2
            · subst j
              simpa [m, hnj, hnu, Nat.cast_add, Nat.cast_ofNat] using
                (input_matrix S W hS hW hSeed a b c d n).2.2.1
            · simpa [m, hnj, hnu, hnl] using
                (input_matrix S W hS hW hSeed a b c d j).2.2.2 n hnj hnu hnl
      have hcore := rec_core_aux S W a b c d j l (b + c + 1)
        (fun n => t n) m (fun n => h (a : ℤ) b c d n) (Λ (a : ℤ) b l)
        hX hE ht_nat hmatn
      have hscalar : (∑ n ∈ Finset.range (b + c + 1),
          (t n / ι (h (a : ℤ) b c d n)) * m n) - ι (Λ (a : ℤ) b l) * t j = 0 := by
        apply unit_scalar_injective_rec S hS
        simpa [Finset.sum_smul, sub_smul] using hcore
      have hjN : j < b + c + 1 := by
        have htri := hj.2.2.2.2.2.2.1
        omega
      have hsparse := rec_sparse_aux (b + c + 1) j
        (ι (Lm2 (a : ℤ) b c d j)) 0 (ι (diagonalEntry (a : ℤ) b c d j))
        (ι (Lp2 (a : ℤ) b c d j))
        (fun n => t n / ι (h (a : ℤ) b c d n)) hjN m (fun n => rfl)
      rw [hsparse] at hscalar
      have hsfin :
          (ι (Lm2 (a : ℤ) b c d j) / ι (h (a : ℤ) b c d ((j : ℤ) - 2))) * t (j - 2) +
          ((ι (diagonalEntry (a : ℤ) b c d j - Λ (a : ℤ) b l * h (a : ℤ) b c d j) /
            ι (h (a : ℤ) b c d j)) * t j) +
          (ι (Lp2 (a : ℤ) b c d j) / ι (h (a : ℤ) b c d ((j : ℤ) + 2))) * t (j + 2) = 0 := by
        rw [hmid]
        by_cases hl2 : 2 ≤ j
        · by_cases hu : j + 2 < b + c + 1
          · simp [hl2, hu, map_sub, map_mul] at hscalar ⊢
            linear_combination hscalar
          · have huadm : ¬ hAdmissible (a : ℤ) b c d ((j : ℤ) + 2) := by
              intro hh
              obtain ⟨_, _, _, _, _, htri, _⟩ := hh.2
              omega
            have hLp : Lp2 (a : ℤ) b c d j = 0 := by simp [Lp2, huadm]
            simp [hl2, hu, hLp, map_sub, map_mul] at hscalar ⊢
            linear_combination hscalar
        · have hladm : ¬ hAdmissible (a : ℤ) b c d ((j : ℤ) - 2) := by
            intro hh
            have hn := hh.1.2.2.1
            omega
          have hLm : Lm2 (a : ℤ) b c d j = 0 := by simp [Lm2, hladm]
          by_cases hu : j + 2 < b + c + 1
          · simp [hl2, hu, hLm, map_sub, map_mul] at hscalar ⊢
            linear_combination hscalar
          · have huadm : ¬ hAdmissible (a : ℤ) b c d ((j : ℤ) + 2) := by
              intro hh
              obtain ⟨_, _, _, _, _, htri, _⟩ := hh.2
              omega
            have hLp : Lp2 (a : ℤ) b c d j = 0 := by simp [Lp2, huadm]
            simp [hl2, hu, hLm, hLp, map_sub, map_mul] at hscalar ⊢
            linear_combination hscalar
      have hfinal := congrArg (fun r : K => r • 𝟙 (𝟙_ C)) hsfin
      simpa [ht, smul_smul, add_smul, map_sub, map_mul] using hfinal
    · rw [rec_overlapTet_zero_int S W hS a b c d (j - 2) l hv,
        rec_overlapTet_zero_int S W hS a b c d j l hv,
        rec_overlapTet_zero_int S W hS a b c d (j + 2) l hv]
      simp
  · simp [diagonalEntry, Lp2, Lm2, h, hj]

theorem solution : QuantumSixJ.NetworkRecurrence.{v,u} := by
  intro C _ _ _ _ _ _ S W hS hW hSeed a b c d j l
  have hrec := overlap_recurrence S W hS hW hSeed a b c d j l
  simpa only [overlap_eq S W hS hW, ← matrix_lower, ← matrix_diag, ← matrix_upper] using hrec
