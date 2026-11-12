-- Prove2me | solution 1 for ZeroOneExpansion.fact_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:38:24.740276+00:00
-- url     : https://prove2.me/submissions/0f277f25-9f28-4b14-812c-69036ec7ecdd

import Mathlib
import Definitions.Def_ZeroOneExpansion_IsPolytope
import Definitions.Def_ZeroOneExpansion_exposedFace
import Definitions.Def_ZeroOneExpansion_IsAdj

set_option autoImplicit false

namespace Aux_ZOE_fact5

open ZeroOneExpansion Matrix

def mkDual {m : ℕ} (c : Fin m → ℝ) : StrongDual ℝ (Fin m → ℝ) :=
  ∑ k : Fin m, c k • ContinuousLinearMap.proj k

lemma mkDual_apply {m : ℕ} (c y : Fin m → ℝ) : mkDual c y = c ⬝ᵥ y := by
  simp [mkDual, dotProduct]

lemma vec_eq_sum_single {m : ℕ} (y : Fin m → ℝ) :
    y = ∑ k : Fin m, y k • Pi.single k (1 : ℝ) := by
  ext j
  simp [Pi.single_apply]

lemma dual_eq_dot {m : ℕ} (L : StrongDual ℝ (Fin m → ℝ)) :
    ∃ c : Fin m → ℝ, ∀ y : Fin m → ℝ, L y = c ⬝ᵥ y := by
  refine ⟨fun k => L (Pi.single k 1), fun y => ?_⟩
  conv_lhs => rw [vec_eq_sum_single y]
  simp [map_sum, map_smul, dotProduct, mul_comm]

def mkDualPi {n : ℕ} {d : Fin n → ℕ} (c : (i : Fin n) → Fin (d i) → ℝ) :
    StrongDual ℝ ((i : Fin n) → Fin (d i) → ℝ) :=
  ∑ i : Fin n, ∑ k : Fin (d i), c i k •
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d i) => ℝ) k).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin n => Fin (d i) → ℝ) i))

lemma mkDualPi_apply {n : ℕ} {d : Fin n → ℕ} (c x : (i : Fin n) → Fin (d i) → ℝ) :
    mkDualPi c x = ∑ i, c i ⬝ᵥ x i := by
  simp [mkDualPi, dotProduct]

lemma pi_eq_sum_single {n : ℕ} {d : Fin n → ℕ} (x : (i : Fin n) → Fin (d i) → ℝ) :
    x = ∑ i : Fin n, ∑ k : Fin (d i), x i k • Pi.single i (Pi.single k (1 : ℝ)) := by
  ext i₀ k₀
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i₀]
  · simp only [Pi.single_eq_same]
    rw [Finset.sum_eq_single k₀]
    · simp
    · intro k _ hk
      simp [hk.symm]
    · intro hk₀; exact absurd (Finset.mem_univ k₀) hk₀
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro k _
    have hne : (Pi.single i (Pi.single k (1 : ℝ)) : (j : Fin n) → Fin (d j) → ℝ) i₀ = 0 := by
      simp [hi.symm]
    simp [hne]
  · intro hi₀; exact absurd (Finset.mem_univ i₀) hi₀

lemma dualPi_eq_sum_dot {n : ℕ} {d : Fin n → ℕ}
    (L : StrongDual ℝ ((i : Fin n) → Fin (d i) → ℝ)) :
    ∃ c : (i : Fin n) → Fin (d i) → ℝ, ∀ x, L x = ∑ i, c i ⬝ᵥ x i := by
  refine ⟨fun i k => L (Pi.single i (Pi.single k 1)), fun x => ?_⟩
  conv_lhs => rw [pi_eq_sum_single x]
  simp [map_sum, map_smul, dotProduct, mul_comm]

lemma exposedFace_pi {n : ℕ} {d : Fin n → ℕ} (P : (i : Fin n) → Set (Fin (d i) → ℝ))
    (c : (i : Fin n) → Fin (d i) → ℝ) :
    exposedFace (Set.univ.pi P) (fun x => ∑ i, c i ⬝ᵥ x i) =
      Set.univ.pi fun i => exposedFace (P i) (fun y => c i ⬝ᵥ y) := by
  ext x
  simp only [exposedFace, Set.mem_univ_pi]
  constructor
  · rintro ⟨hxP, hmax⟩ i
    refine ⟨hxP i, fun y hy => ?_⟩
    let z := Function.update x i y
    have hzP : ∀ j, z j ∈ P j := by
      intro j
      by_cases hj : j = i
      · subst hj; simpa [z] using hy
      · simpa [z, hj] using hxP j
    have hle := hmax z hzP
    have hdiff :
        (∑ j ∈ Finset.univ.erase i, c j ⬝ᵥ z j) =
          ∑ j ∈ Finset.univ.erase i, c j ⬝ᵥ x j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hne : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [z, hne]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ (fun j => c j ⬝ᵥ x j) (Finset.mem_univ i)] at hle
    simp only [z, Function.update_self, hdiff] at hle
    linarith
  · intro hx
    refine ⟨fun i => (hx i).1, fun z hz => ?_⟩
    exact Finset.sum_le_sum fun i _ => (hx i).2 (z i) (hz i)

lemma isExposed_pi_nonempty_iff {n : ℕ} {d : Fin n → ℕ}
    (P : (i : Fin n) → Set (Fin (d i) → ℝ))
    {F : Set ((i : Fin n) → Fin (d i) → ℝ)} (hFne : F.Nonempty) :
    IsExposed ℝ (Set.univ.pi P) F ↔
      ∃ G : (i : Fin n) → Set (Fin (d i) → ℝ),
        (∀ i, (G i).Nonempty ∧ IsExposed ℝ (P i) (G i)) ∧ F = Set.univ.pi G := by
  constructor
  · intro hF
    obtain ⟨L, hL⟩ := hF hFne
    obtain ⟨c, hc⟩ := dualPi_eq_sum_dot L
    have hFeq : F = exposedFace (Set.univ.pi P) (fun x => ∑ i, c i ⬝ᵥ x i) := by
      rw [hL]
      ext x
      simp [exposedFace, hc]
    rw [exposedFace_pi] at hFeq
    obtain ⟨x₀, hx₀⟩ := hFne
    have hx₀' : x₀ ∈ Set.univ.pi (fun i => exposedFace (P i) (fun y => c i ⬝ᵥ y)) :=
      hFeq ▸ hx₀
    refine ⟨fun i => exposedFace (P i) (fun y => c i ⬝ᵥ y), fun i => ⟨⟨x₀ i, hx₀' i trivial⟩, ?_⟩, hFeq⟩
    intro _
    refine ⟨mkDual (c i), ?_⟩
    ext y
    simp [exposedFace, mkDual_apply]
  · rintro ⟨G, hG, rfl⟩
    have hex : ∀ i, ∃ ci : Fin (d i) → ℝ, G i = exposedFace (P i) (fun y => ci ⬝ᵥ y) := by
      intro i
      obtain ⟨Li, hLi⟩ := (hG i).2 (hG i).1
      obtain ⟨ci, hci⟩ := dual_eq_dot Li
      refine ⟨ci, ?_⟩
      rw [hLi]
      ext y
      simp [exposedFace, hci]
    choose c hc using hex
    intro _
    refine ⟨mkDualPi c, ?_⟩
    have hGeq : Set.univ.pi G = exposedFace (Set.univ.pi P) (fun x => ∑ i, c i ⬝ᵥ x i) := by
      rw [exposedFace_pi]
      ext x
      simp [hc]
    rw [hGeq]
    ext x
    simp [exposedFace, mkDualPi_apply]

lemma direction_affineSpan_pi {n : ℕ} {d : Fin n → ℕ}
    (G : (i : Fin n) → Set (Fin (d i) → ℝ))
    {x₀ : (i : Fin n) → Fin (d i) → ℝ} (hx₀ : x₀ ∈ Set.univ.pi G) :
    (affineSpan ℝ (Set.univ.pi G)).direction =
      Submodule.pi Set.univ (fun i => (affineSpan ℝ (G i)).direction) := by
  apply le_antisymm
  · rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    intro v hv i _
    rcases hv with ⟨a, ha, b, hb, rfl⟩
    change a i -ᵥ b i ∈ (affineSpan ℝ (G i)).direction
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan ℝ (ha i trivial) (hb i trivial)
  · intro v hv
    have hv_sum : v = ∑ i : Fin n, Pi.single i (v i) := by
      ext i k
      simp only [Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro c _ hc
        have h0 : (Pi.single c (v c) : (j : Fin n) → Fin (d j) → ℝ) i = 0 := by
          simp [hc.symm]
        simp [h0]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hv_sum]
    apply Submodule.sum_mem
    intro i _
    let linSingle : (Fin (d i) → ℝ) →ₗ[ℝ] ((j : Fin n) → Fin (d j) → ℝ) :=
      LinearMap.single ℝ (fun j => Fin (d j) → ℝ) i
    change linSingle (v i) ∈ (affineSpan ℝ (Set.univ.pi G)).direction
    have hvi : v i ∈ vectorSpan ℝ (G i) := by
      rw [← direction_affineSpan]
      exact hv i trivial
    have hle : vectorSpan ℝ (G i) ≤
        ((affineSpan ℝ (Set.univ.pi G)).direction).comap linSingle := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro w ⟨a, ha, b, hb, rfl⟩
      simp only [Set.mem_preimage, SetLike.mem_coe, Submodule.mem_comap,
        direction_affineSpan]
      let za := Function.update x₀ i a
      let zb := Function.update x₀ i b
      have hza : za ∈ Set.univ.pi G := by
        intro j _
        by_cases hj : j = i
        · subst hj; simpa [za] using ha
        · simpa [za, hj] using hx₀ j trivial
      have hzb : zb ∈ Set.univ.pi G := by
        intro j _
        by_cases hj : j = i
        · subst hj; simpa [zb] using hb
        · simpa [zb, hj] using hx₀ j trivial
      have hdiff : linSingle (a -ᵥ b) = za -ᵥ zb := by
        ext j k
        by_cases hj : j = i
        · subst hj
          simp [linSingle, za, zb]
        · simp [linSingle, za, zb, hj]
      rw [hdiff]
      exact vsub_mem_vectorSpan ℝ hza hzb
    exact hle hvi

noncomputable def submodulePiEquiv {n : ℕ} {d : Fin n → ℕ}
    (M : (i : Fin n) → Submodule ℝ (Fin (d i) → ℝ)) :
    Submodule.pi Set.univ M ≃ₗ[ℝ] ((i : Fin n) → M i) where
  toFun v i := ⟨v.1 i, v.2 i trivial⟩
  invFun f := ⟨fun i => (f i).1, fun i _ => (f i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

lemma finrank_affineSpan_pi {n : ℕ} {d : Fin n → ℕ}
    (G : (i : Fin n) → Set (Fin (d i) → ℝ))
    {x₀ : (i : Fin n) → Fin (d i) → ℝ} (hx₀ : x₀ ∈ Set.univ.pi G) :
    Module.finrank ℝ (affineSpan ℝ (Set.univ.pi G)).direction =
      ∑ i : Fin n, Module.finrank ℝ (affineSpan ℝ (G i)).direction := by
  let M : (i : Fin n) → Submodule ℝ (Fin (d i) → ℝ) :=
    fun i => (affineSpan ℝ (G i)).direction
  rw [direction_affineSpan_pi G hx₀]
  change Module.finrank ℝ (Submodule.pi Set.univ M) = ∑ i : Fin n, Module.finrank ℝ (M i)
  rw [(submodulePiEquiv M).finrank_eq, Module.finrank_pi_fintype]

lemma sum_eq_one_iff {n : ℕ} (f : Fin n → ℕ) :
    (∑ i : Fin n, f i) = 1 ↔ ∃ j : Fin n, f j = 1 ∧ ∀ i, i ≠ j → f i = 0 := by
  constructor
  · intro hsum
    have hex : ∃ j : Fin n, f j ≠ 0 := by
      by_contra hall
      push_neg at hall
      have : (∑ i : Fin n, f i) = 0 := Finset.sum_eq_zero fun i _ => hall i
      omega
    obtain ⟨j, hj⟩ := hex
    refine ⟨j, ?_, ?_⟩
    · have hle : f j ≤ ∑ i : Fin n, f i :=
        Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    · intro i hi
      have hsub : ({j, i} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
      have hle := Finset.sum_le_sum_of_subset (f := f) hsub
      rw [Finset.sum_pair hi.symm] at hle
      omega
  · rintro ⟨j, hj1, hj0⟩
    rw [Finset.sum_eq_single j]
    · exact hj1
    · intro i _ hi; exact hj0 i hi
    · intro hj; exact absurd (Finset.mem_univ j) hj

lemma vertices_pi {n : ℕ} {d : Fin n → ℕ} (P : (i : Fin n) → Set (Fin (d i) → ℝ)) :
    {x | IsVertexOf (Set.univ.pi P) x} = Set.univ.pi (fun i => {y | IsVertexOf (P i) y}) := by
  ext x
  simp only [Set.mem_univ_pi, IsVertexOf]
  change IsExposed ℝ (Set.univ.pi P) {x} ↔ ∀ i, IsExposed ℝ (P i) {x i}
  constructor
  · intro hx i
    obtain ⟨G, hG, hEq⟩ := (isExposed_pi_nonempty_iff P (Set.singleton_nonempty x)).mp hx
    have hGi : G i = {x i} := by
      ext y
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hy
        have hmem : Function.update x i y ∈ Set.univ.pi G := by
          intro k _
          by_cases hk : k = i
          · subst hk; simpa using hy
          · have hxG : x ∈ Set.univ.pi G := hEq ▸ Set.mem_singleton x
            simpa [hk] using hxG k trivial
        have hux : Function.update x i y = x := Set.mem_singleton_iff.mp (hEq ▸ hmem)
        have := congr_fun hux i
        simpa using this
      · rintro rfl
        have hxG : x ∈ Set.univ.pi G := hEq ▸ Set.mem_singleton x
        exact hxG i trivial
    exact hGi ▸ (hG i).2
  · intro hx
    have hEq : ({x} : Set ((i : Fin n) → Fin (d i) → ℝ)) = Set.univ.pi (fun i => {x i}) := by
      ext z
      simp [funext_iff]
    rw [hEq]
    exact (isExposed_pi_nonempty_iff P (hEq ▸ Set.singleton_nonempty x)).mpr
      ⟨fun i => {x i}, fun i => ⟨Set.singleton_nonempty (x i), hx i⟩, rfl⟩

end Aux_ZOE_fact5

open ZeroOneExpansion Matrix Aux_ZOE_fact5

theorem solution (n : ℕ) (hn : 1 ≤ n) (d : Fin n → ℕ) (P : (i : Fin n) → Set (Fin (d i) → ℝ))
    (hP : ∀ i, IsPolytope (P i)) :
    (∀ c : (i : Fin n) → Fin (d i) → ℝ,
      exposedFace (Set.univ.pi P) (fun x => ∑ i, c i ⬝ᵥ x i) =
        Set.univ.pi fun i => exposedFace (P i) (fun y => c i ⬝ᵥ y)) ∧
    {x | IsVertexOf (Set.univ.pi P) x} = Set.univ.pi (fun i => {y | IsVertexOf (P i) y}) ∧
    ∀ x y : (i : Fin n) → Fin (d i) → ℝ,
      IsVertexOf (Set.univ.pi P) x → IsVertexOf (Set.univ.pi P) y → x ≠ y →
        (IsAdj (Set.univ.pi P) x y ↔
          ∃ j : Fin n, (∀ i, i ≠ j → x i = y i) ∧ IsAdj (P j) (x j) (y j)) := by
  let _ := hn
  let _ := hP
  refine ⟨exposedFace_pi P, vertices_pi P, ?_⟩
  intro x y hx hy hxy
  have hxv : ∀ i, IsVertexOf (P i) (x i) := by
    intro i
    have hmem := (Set.ext_iff.mp (vertices_pi P) x).mp hx
    exact hmem i trivial
  have hyv : ∀ i, IsVertexOf (P i) (y i) := by
    intro i
    have hmem := (Set.ext_iff.mp (vertices_pi P) y).mp hy
    exact hmem i trivial
  constructor
  · rintro ⟨_, _, _, F, hFexp, hFdim, hxF, hyF⟩
    obtain ⟨G, hG, rfl⟩ := (isExposed_pi_nonempty_iff P ⟨x, hxF⟩).mp hFexp
    rw [finrank_affineSpan_pi G hxF, sum_eq_one_iff] at hFdim
    obtain ⟨j, hj1, hj0⟩ := hFdim
    have heq_other : ∀ i, i ≠ j → x i = y i := by
      intro i hi
      have hbot : (affineSpan ℝ (G i)).direction = ⊥ :=
        Submodule.finrank_eq_zero.mp (hj0 i hi)
      have hvsub : x i -ᵥ y i ∈ (affineSpan ℝ (G i)).direction := by
        rw [direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ (hxF i trivial) (hyF i trivial)
      rw [hbot, Submodule.mem_bot] at hvsub
      exact sub_eq_zero.mp hvsub
    have hne_j : x j ≠ y j := by
      intro hxj
      apply hxy
      funext i
      by_cases hi : i = j
      · subst hi; exact hxj
      · exact heq_other i hi
    exact ⟨j, heq_other, hne_j, hxv j, hyv j, G j, (hG j).2, hj1, hxF j trivial, hyF j trivial⟩
  · rintro ⟨j, heq_other, _, _, _, Fj, hFj_exp, hFj_dim, hxj, hyj⟩
    let G : (i : Fin n) → Set (Fin (d i) → ℝ) :=
      Function.update (fun i => ({x i} : Set (Fin (d i) → ℝ))) j Fj
    have hxG : x ∈ Set.univ.pi G := by
      intro i _
      by_cases hi : i = j
      · subst hi; simpa [G] using hxj
      · simp [G, hi]
    have hyG : y ∈ Set.univ.pi G := by
      intro i _
      by_cases hi : i = j
      · subst hi; simpa [G] using hyj
      · simp [G, hi, ← heq_other i hi]
    have hG_exp : ∀ i, (G i).Nonempty ∧ IsExposed ℝ (P i) (G i) := by
      intro i
      refine ⟨⟨x i, hxG i trivial⟩, ?_⟩
      by_cases hi : i = j
      · subst hi; simpa [G] using hFj_exp
      · have hGi : G i = {x i} := by simp [G, hi]
        rw [hGi]
        exact hxv i
    have hFexp : IsExposed ℝ (Set.univ.pi P) (Set.univ.pi G) :=
      (isExposed_pi_nonempty_iff P ⟨x, hxG⟩).mpr ⟨G, hG_exp, rfl⟩
    have hFdim : Module.finrank ℝ (affineSpan ℝ (Set.univ.pi G)).direction = 1 := by
      rw [finrank_affineSpan_pi G hxG, sum_eq_one_iff]
      refine ⟨j, ?_, ?_⟩
      · have hGj : G j = Fj := by simp [G]
        rw [hGj]
        exact hFj_dim
      · intro i hi
        have hGi : G i = {x i} := by simp [G, hi]
        rw [hGi, direction_affineSpan, vectorSpan_singleton, finrank_bot]
    exact ⟨hxy, hx, hy, Set.univ.pi G, hFexp, hFdim, hxG, hyG⟩
