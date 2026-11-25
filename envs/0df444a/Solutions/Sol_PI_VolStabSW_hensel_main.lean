-- Prove2me | solution 1 for PI.VolStabSW.hensel_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:09.579737+00:00
-- url     : https://prove2.me/submissions/5fb87d50-1be4-4057-9ce3-d1376ae50da4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HenselCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HenselCountHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabSW
open MeasureTheory Topology
section Hensel
variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
private theorem mem_hlev_iff {Λ0 : AddSubgroup V} {H : AddSubgroup X} {G : V → X} {y : V} {h : X}
    {Z : V} : Z ∈ hlev Λ0 H G y h ↔ Z ∈ Λ0 ∧ G (y + Z) - h ∈ H := Iff.rfl
private theorem isOpen_of_add_openSubgroup_stable (U : AddSubgroup V) (hU : IsOpen (U : Set V)) (A : Set V)
    (hA : ∀ Z ∈ A, ∀ W ∈ U, Z + W ∈ A) : IsOpen A := by
  rw [isOpen_iff_forall_mem_open]
  intro Z hZ
  refine ⟨(fun W => -Z + W) ⁻¹' (U : Set V), ?_, ?_, ?_⟩
  · intro W hW
    have h := hA Z hZ (-Z + W) hW
    simpa using h
  · exact hU.preimage (continuous_const_add (-Z))
  · show -Z + Z ∈ (U : Set V)
    simp
private theorem finite_image_mk_of_isOpen_of_isCompact' (K L : AddSubgroup X) (hKo : IsOpen (K : Set X))
    (hLc : IsCompact (L : Set X)) :
    ((QuotientAddGroup.mk : X → X ⧸ K) '' (L : Set X)).Finite := by
  obtain ⟨T, hT⟩ := hLc.elim_finite_subcover (fun x : X => (fun z => -x + z) ⁻¹' (K : Set X))
    (fun x => hKo.preimage (continuous_const_add (-x)))
    (fun l _ => Set.mem_iUnion.2 ⟨l, by simp⟩)
  refine (T.finite_toSet.image (QuotientAddGroup.mk : X → X ⧸ K)).subset ?_
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨x, hx, hlx⟩ := Set.mem_iUnion₂.1 (hT hl)
  exact ⟨x, hx, QuotientAddGroup.eq.2 hlx⟩
private theorem measure_mul_eq_of_const_fibres (μ : Measure V) (ν : Measure X) [ν.IsAddHaarMeasure]
    (K L : AddSubgroup X) (hKL : K ≤ L) (hKo : IsOpen (K : Set X)) (hLc : IsCompact (L : Set X))
    (P : Set V) (f : V → X) (hfP : ∀ Z ∈ P, f Z ∈ L) (m : ENNReal)
    (hmeas : ∀ t ∈ L, MeasurableSet {Z | Z ∈ P ∧ f Z - t ∈ K})
    (hm : ∀ t ∈ L, μ {Z | Z ∈ P ∧ f Z - t ∈ K} = m) :
    μ P * ν K = m * ν L := by
  classical
  have hF := finite_image_mk_of_isOpen_of_isCompact' K L hKo hLc
  have hqeq : ∀ a b : X, ((a : X ⧸ K) = (b : X ⧸ K) ↔ a - b ∈ K) := by
    intro a b
    rw [QuotientAddGroup.eq]
    constructor
    · intro h
      have := K.neg_mem h
      convert this using 1
      abel
    · intro h
      have := K.neg_mem h
      convert this using 1
      abel
  have hC : ∀ c, c ∈ hF.toFinset ↔ ∃ t ∈ L, (t : X ⧸ K) = c := by
    intro c
    rw [Set.Finite.mem_toFinset, Set.mem_image]
    rfl
  let A : X ⧸ K → Set V := fun c => {Z | Z ∈ P ∧ (f Z : X ⧸ K) = c}
  let B : X ⧸ K → Set X := fun c => (QuotientAddGroup.mk : X → X ⧸ K) ⁻¹' {c}
  have hA : ∀ c ∈ hF.toFinset, MeasurableSet (A c) ∧ μ (A c) = m := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := (hC c).1 hc
    have e : A (t : X ⧸ K) = {Z | Z ∈ P ∧ f Z - t ∈ K} := by
      ext Z
      simp only [A, Set.mem_setOf_eq, hqeq]
    rw [e]
    exact ⟨hmeas t ht, hm t ht⟩
  have hB : ∀ c ∈ hF.toFinset, MeasurableSet (B c) ∧ ν (B c) = ν K := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := (hC c).1 hc
    have e : B (t : X ⧸ K) = (fun x => -t + x) ⁻¹' (K : Set X) := by
      ext x
      simp only [B, Set.mem_preimage, Set.mem_singleton_iff, hqeq, SetLike.mem_coe,
        sub_eq_neg_add]
    rw [e, measure_preimage_add]
    exact ⟨(hKo.preimage (continuous_const_add (-t))).measurableSet, rfl⟩
  have hPU : P = ⋃ c ∈ hF.toFinset, A c := by
    ext Z
    simp only [Set.mem_iUnion, A, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hZ
      exact ⟨(f Z : X ⧸ K), (hC _).2 ⟨f Z, hfP Z hZ, rfl⟩, hZ, rfl⟩
    · rintro ⟨c, -, hZ, -⟩
      exact hZ
  have hLU : (L : Set X) = ⋃ c ∈ hF.toFinset, B c := by
    ext x
    simp only [Set.mem_iUnion, B, Set.mem_preimage, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      exact ⟨(x : X ⧸ K), (hC _).2 ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨c, hc, hxc⟩
      obtain ⟨t, ht, rfl⟩ := (hC c).1 hc
      have h1 := hKL ((hqeq x t).1 hxc)
      have h2 := L.add_mem h1 ht
      simpa using h2
  have hdA : (hF.toFinset : Set (X ⧸ K)).PairwiseDisjoint A := by
    intro c _ c' _ hne
    show Disjoint (A c) (A c')
    rw [Set.disjoint_left]
    intro Z h1 h2
    have h1' : Z ∈ P ∧ (f Z : X ⧸ K) = c := h1
    have h2' : Z ∈ P ∧ (f Z : X ⧸ K) = c' := h2
    exact hne (h1'.2.symm.trans h2'.2)
  have hdB : (hF.toFinset : Set (X ⧸ K)).PairwiseDisjoint B := by
    intro c _ c' _ hne
    show Disjoint (B c) (B c')
    rw [Set.disjoint_left]
    intro x h1 h2
    have h1' : (x : X ⧸ K) = c := h1
    have h2' : (x : X ⧸ K) = c' := h2
    exact hne (h1'.symm.trans h2')
  have hμP : μ P = hF.toFinset.card * m := by
    rw [hPU, measure_biUnion_finset hdA (fun c hc => (hA c hc).1),
      Finset.sum_congr rfl (fun c hc => (hA c hc).2), Finset.sum_const, nsmul_eq_mul]
  have hνL : ν L = hF.toFinset.card * ν K := by
    have hLU' : ν (L : Set X) = ν (⋃ c ∈ hF.toFinset, B c) := congrArg ν hLU
    rw [hLU', measure_biUnion_finset hdB (fun c hc => (hB c hc).1),
      Finset.sum_congr rfl (fun c hc => (hB c hc).2), Finset.sum_const, nsmul_eq_mul]
  rw [hμP, hνL]
  ring
private theorem ennreal_mul_cross_cancel {a b c d e f : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h1 : a * f = b * c) (h2 : a * d = e * c) : b * d = e * f := by
  have h3 : b * d * c = e * f * c := by
    calc b * d * c = (b * c) * d := by ring
      _ = (a * f) * d := by rw [h1]
      _ = (a * d) * f := by ring
      _ = (e * c) * f := by rw [h2]
      _ = e * f * c := by ring
  calc b * d = b * d * (c * c⁻¹) := by rw [ENNReal.mul_inv_cancel hc0 hct, mul_one]
    _ = (b * d * c) * c⁻¹ := (mul_assoc _ _ _).symm
    _ = (e * f * c) * c⁻¹ := by rw [h3]
    _ = e * f := by rw [mul_assoc, ENNReal.mul_inv_cancel hc0 hct, mul_one]
end Hensel
end PI.VolStabSW
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology
variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
namespace PI.VolStabSW
theorem _root_.solution (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (G : V → X) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (h : X) (hh : h - G y ∈ H 0) (n : ℕ) :
    μ (hlev (Λ 0) (H n) G y h) * ν (H 0) = μ (Λ 0) * ν (H n) := by
  have hΛ0 : ∀ k, Λ k ≤ Λ 0 := fun k => hΛa (Nat.zero_le k)
  have hHa : ∀ k l, k ≤ l → H l ≤ H k := by
    intro k l hkl
    rw [← hD k, ← hD l]
    exact AddSubgroup.map_mono (hΛa hkl)
  have hDm : ∀ k, ∀ W ∈ Λ k, D W ∈ H k := by
    intro k W hW
    rw [← hD k]
    exact AddSubgroup.mem_map_of_mem D hW
  have hDs : ∀ k, ∀ t ∈ H k, ∃ W ∈ Λ k, D W = t := by
    intro k t ht
    rw [← hD k] at ht
    exact AddSubgroup.mem_map.1 ht
  have hstep : ∀ k, ∀ Z ∈ Λ 0, ∀ W ∈ Λ k, G (y + (Z + W)) - G (y + Z) - D W ∈ H (k + 1) := by
    intro k Z hZ W hW
    have := hG k Z hZ W hW
    rwa [add_assoc y Z W] at this
  have hstab : ∀ k h', ∀ Z ∈ hlev (Λ 0) (H k) G y h', ∀ W ∈ Λ k,
      Z + W ∈ hlev (Λ 0) (H k) G y h' := by
    intro k h' Z hZ W hW
    rw [mem_hlev_iff] at hZ ⊢
    refine ⟨(Λ 0).add_mem hZ.1 (hΛ0 k hW), ?_⟩
    have h1 := hHa k (k + 1) (Nat.le_succ k) (hstep k Z hZ.1 W hW)
    have h2 := (H k).add_mem ((H k).add_mem h1 hZ.2) (hDm k W hW)
    convert h2 using 1
    abel
  have hopen : ∀ k h', IsOpen (hlev (Λ 0) (H k) G y h') :=
    fun k h' => isOpen_of_add_openSubgroup_stable (Λ k) (hΛo k) _ (hstab k h')
  have key : ∀ k, ∀ h', h' - G y ∈ H 0 →
      μ (hlev (Λ 0) (H k) G y h') * ν (H 0) = μ (Λ 0) * ν (H k) := by
    intro k
    induction k with
    | zero =>
      intro h' hh'
      have e : hlev (Λ 0) (H 0) G y h' = (Λ 0 : Set V) := by
        ext Z
        rw [mem_hlev_iff]
        constructor
        · exact fun hZ => hZ.1
        · intro hZ
          refine ⟨hZ, ?_⟩
          have h1 := hHa 0 1 (Nat.zero_le 1) (hstep 0 0 (Λ 0).zero_mem Z hZ)
          have h2 := (H 0).sub_mem ((H 0).add_mem h1 (hDm 0 Z hZ)) hh'
          convert h2 using 1
          simp only [add_zero, zero_add]
          abel
      rw [e]
    | succ k ih =>
      intro h' hh'
      have hpiece : ∀ t ∈ H k,
          {Z | Z ∈ hlev (Λ 0) (H k) G y h' ∧ (G (y + Z) - h') - t ∈ H (k + 1)}
            = hlev (Λ 0) (H (k + 1)) G y (h' + t) := by
        intro t ht
        ext Z
        simp only [Set.mem_setOf_eq, mem_hlev_iff]
        constructor
        · rintro ⟨⟨hZ, -⟩, h2⟩
          refine ⟨hZ, ?_⟩
          rw [← sub_sub]
          exact h2
        · rintro ⟨hZ, h2⟩
          rw [← sub_sub] at h2
          refine ⟨⟨hZ, ?_⟩, h2⟩
          have := (H k).add_mem (hHa k (k + 1) (Nat.le_succ k) h2) ht
          simpa using this
      have htrans : ∀ t ∈ H k, μ (hlev (Λ 0) (H (k + 1)) G y (h' + t))
          = μ (hlev (Λ 0) (H (k + 1)) G y h') := by
        intro t ht
        obtain ⟨W, hW, rfl⟩ := hDs k t ht
        have hW0 := hΛ0 k hW
        have e : hlev (Λ 0) (H (k + 1)) G y h' =
            (fun Z => W + Z) ⁻¹' hlev (Λ 0) (H (k + 1)) G y (h' + D W) := by
          ext Z
          simp only [Set.mem_preimage, mem_hlev_iff]
          constructor
          · rintro ⟨hZ, h2⟩
            refine ⟨(Λ 0).add_mem hW0 hZ, ?_⟩
            have h3 := (H (k + 1)).add_mem (hstep k Z hZ W hW) h2
            convert h3 using 1
            rw [add_comm W Z]
            abel
          · rintro ⟨hWZ, h2⟩
            have hZ : Z ∈ Λ 0 := by
              have := (Λ 0).sub_mem hWZ hW0
              simpa using this
            refine ⟨hZ, ?_⟩
            have h3 := (H (k + 1)).sub_mem h2 (hstep k Z hZ W hW)
            convert h3 using 1
            rw [add_comm W Z]
            abel
        rw [e, measure_preimage_add]
      have hc := measure_mul_eq_of_const_fibres μ ν (H (k + 1)) (H k) (hHa k (k + 1) (Nat.le_succ k))
        (hHo (k + 1)) (hHc k) (hlev (Λ 0) (H k) G y h') (fun Z => G (y + Z) - h')
        (fun Z hZ => (mem_hlev_iff.1 hZ).2) (μ (hlev (Λ 0) (H (k + 1)) G y h'))
        (fun t ht => by rw [hpiece t ht]; exact (hopen (k + 1) (h' + t)).measurableSet)
        (fun t ht => by rw [hpiece t ht]; exact htrans t ht)
      have hne0 : ν (H k : Set X) ≠ 0 := (hHo k).measure_ne_zero ν ⟨0, (H k).zero_mem⟩
      have hnetop : ν (H k : Set X) ≠ ⊤ := (hHc k).measure_lt_top.ne
      exact ennreal_mul_cross_cancel hne0 hnetop hc (ih h' hh')
  exact key n h hh
end PI.VolStabSW
