-- Prove2me | solution 1 for PI.VolStabS.hensel_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:52.418468+00:00
-- url     : https://prove2.me/submissions/66bf4a33-0793-41d8-b146-bd8daf6225d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_HenselCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_HenselCountHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Topology
variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
namespace PI.VolStabS
theorem _root_.solution (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (G : V → X) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (h : X) (hh : h - G y ∈ H 0) (n : ℕ) :
    μ (hlev (Λ 0) (H n) G y h) * ν (H 0) = μ (Λ 0) * ν (H n) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : V → X, ∀ Z, f Z = G (y + Z) - h := ⟨_, fun _ => rfl⟩
  have memS : ∀ m Z, Z ∈ hlev (Λ 0) (H m) G y h ↔ Z ∈ Λ 0 ∧ f Z ∈ H m := by
    intro m Z; rw [hf]; rfl
  have hHa : ∀ m, H (m + 1) ≤ H m := fun m => by
    rw [← hD, ← hD]; exact AddSubgroup.map_mono (hΛa (Nat.le_succ m))
  have hΛ0 : ∀ m, Λ m ≤ Λ 0 := fun m => hΛa (Nat.zero_le m)
  have hDm : ∀ m, ∀ W ∈ Λ m, D W ∈ H m := fun m W hW => by
    rw [← hD]; exact AddSubgroup.mem_map_of_mem D hW

  have hstep : ∀ m, ∀ Z ∈ Λ 0, ∀ W ∈ Λ m, f (Z + W) - f Z - D W ∈ H (m + 1) := by
    intro m Z hZ W hW
    have e := hG m Z hZ W hW
    have : f (Z + W) - f Z - D W = G (y + Z + W) - G (y + Z) - D W := by
      rw [hf, hf, ← add_assoc]; abel
    rw [this]; exact e

  have hinv : ∀ m, ∀ Z ∈ hlev (Λ 0) (H m) G y h, ∀ W ∈ Λ m, Z + W ∈ hlev (Λ 0) (H m) G y h := by
    intro m Z hZ W hW
    rw [memS] at hZ ⊢
    refine ⟨(Λ 0).add_mem hZ.1 (hΛ0 m hW), ?_⟩
    have e := hstep m Z hZ.1 W hW
    have : f (Z + W) = (f (Z + W) - f Z - D W) + f Z + D W := by abel
    rw [this]
    exact (H m).add_mem ((H m).add_mem (hHa m e) hZ.2) (hDm m W hW)
  have hopen : ∀ m, IsOpen (hlev (Λ 0) (H m) G y h) := by
    intro m
    rw [isOpen_iff_forall_mem_open]
    intro Z hZ
    refine ⟨(fun u => -Z + u) ⁻¹' (Λ m : Set V), ?_,
      (hΛo m).preimage (continuous_const.add continuous_id), ?_⟩
    · intro u hu
      have := hinv m Z hZ _ hu
      have e : Z + (-Z + u) = u := by abel
      rw [e] at this; exact this
    · show -Z + Z ∈ Λ m
      rw [neg_add_cancel]; exact (Λ m).zero_mem
  have hsub : ∀ m, hlev (Λ 0) (H (m + 1)) G y h ⊆ hlev (Λ 0) (H m) G y h := by
    intro m Z hZ
    rw [memS] at hZ ⊢
    exact ⟨hZ.1, hHa m hZ.2⟩
  induction n with
  | zero =>
    have hS0 : hlev (Λ 0) (H 0) G y h = (Λ 0 : Set V) := by
      ext Z
      rw [memS]
      refine ⟨And.left, fun hZ => ⟨hZ, ?_⟩⟩
      have e := hstep 0 0 (Λ 0).zero_mem Z hZ
      have h0 : f 0 ∈ H 0 := by
        have : f 0 = -(h - G y) := by rw [hf, add_zero]; abel
        rw [this]; exact (H 0).neg_mem hh
      have : f Z = (f (0 + Z) - f 0 - D Z) + f 0 + D Z := by rw [zero_add]; abel
      rw [this]
      exact (H 0).add_mem ((H 0).add_mem (hHa 0 e) h0) (hDm 0 Z hZ)
    rw [hS0]
  | succ m ih =>

    haveI : DiscreteTopology (X ⧸ H (m + 1)) := QuotientAddGroup.discreteTopology (hHo (m + 1))
    set C : Set (X ⧸ H (m + 1)) := (QuotientAddGroup.mk : X → X ⧸ H (m + 1)) '' (H m : Set X)
      with hC
    have hCf : C.Finite := ((hHc m).image QuotientAddGroup.continuous_mk).finite_of_discrete
    haveI : Fintype C := hCf.fintype
    have hxc : ∀ c : C, ∃ u ∈ H m, (u : X ⧸ H (m + 1)) = c := fun c => c.2
    choose x hxm hxq using hxc
    have htc : ∀ c : C, ∃ W ∈ Λ m, D W = x c := by
      intro c
      have := hxm c
      rw [← hD] at this
      exact AddSubgroup.mem_map.1 this
    choose t htm htD using htc
    have hcov : ∀ u ∈ H m, ∃ c : C, -x c + u ∈ H (m + 1) := by
      intro u hu
      refine ⟨⟨(u : X ⧸ H (m + 1)), u, hu, rfl⟩, ?_⟩
      rw [← QuotientAddGroup.eq, hxq]
    have hinj : ∀ c d : C, -x c + x d ∈ H (m + 1) → c = d := by
      intro c d hcd
      apply Subtype.ext
      rw [← hxq c, ← hxq d]
      exact QuotientAddGroup.eq.2 hcd
    have hne : Nonempty C := ⟨(hcov 0 (H m).zero_mem).choose⟩

    have hAi : ∀ c Z, Z ∈ (fun Z => -t c + Z) ⁻¹' hlev (Λ 0) (H (m + 1)) G y h →
        -x c + f Z ∈ H (m + 1) := by
      intro c Z hZ
      have hZ' := (memS _ _).1 hZ
      have e := hstep m (-t c + Z) hZ'.1 (t c) (htm c)
      have e2 : -t c + Z + t c = Z := by abel
      rw [e2, htD] at e
      have : -x c + f Z = (f Z - f (-t c + Z) - x c) + f (-t c + Z) := by abel
      rw [this]
      exact (H (m + 1)).add_mem e hZ'.2
    have hμ : μ (hlev (Λ 0) (H m) G y h) =
        (Fintype.card C : ENNReal) * μ (hlev (Λ 0) (H (m + 1)) G y h) := by
      have hU : hlev (Λ 0) (H m) G y h =
          ⋃ c : C, (fun Z => -t c + Z) ⁻¹' hlev (Λ 0) (H (m + 1)) G y h := by
        ext Z
        simp only [Set.mem_iUnion, Set.mem_preimage]
        constructor
        · intro hZ
          have hZ' := (memS _ _).1 hZ
          obtain ⟨c, hc⟩ := hcov (f Z) hZ'.2
          refine ⟨c, (memS _ _).2 ⟨(Λ 0).add_mem ((Λ 0).neg_mem (hΛ0 m (htm c))) hZ'.1, ?_⟩⟩
          have e := hstep m (-t c + Z) ((Λ 0).add_mem ((Λ 0).neg_mem (hΛ0 m (htm c))) hZ'.1)
            (t c) (htm c)
          have e2 : -t c + Z + t c = Z := by abel
          rw [e2, htD] at e
          have : f (-t c + Z) = -(f Z - f (-t c + Z) - x c) + (-x c + f Z) := by abel
          rw [this]
          exact (H (m + 1)).add_mem ((H (m + 1)).neg_mem e) hc
        · rintro ⟨c, hc⟩
          have := hinv m _ (hsub m hc) (t c) (htm c)
          have e2 : -t c + Z + t c = Z := by abel
          rwa [e2] at this
      rw [hU, measure_iUnion, tsum_fintype]
      · simp only [measure_preimage_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      · intro c d hcd
        rw [Function.onFun, Set.disjoint_left]
        intro Z hc hd
        apply hcd
        apply hinj
        have a1 := hAi c Z hc
        have a2 := hAi d Z hd
        have : -x c + x d = (-x c + f Z) - (-x d + f Z) := by abel
        rw [this]; exact (H (m + 1)).sub_mem a1 a2
      · intro c
        exact ((hopen (m + 1)).preimage (continuous_const.add continuous_id)).measurableSet
    have hν : ν (H m) = (Fintype.card C : ENNReal) * ν (H (m + 1)) := by
      have hU : (H m : Set X) = ⋃ c : C, (fun u => -x c + u) ⁻¹' (H (m + 1) : Set X) := by
        ext u
        simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · intro hu; exact hcov u hu
        · rintro ⟨c, hc⟩
          have : u = x c + (-x c + u) := by abel
          rw [this]; exact (H m).add_mem (hxm c) (hHa m hc)
      rw [hU, measure_iUnion, tsum_fintype]
      · simp only [measure_preimage_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      · intro c d hcd
        rw [Function.onFun, Set.disjoint_left]
        intro u hc hd
        apply hcd
        apply hinj
        simp only [Set.mem_preimage, SetLike.mem_coe] at hc hd
        have : -x c + x d = (-x c + u) - (-x d + u) := by abel
        rw [this]; exact (H (m + 1)).sub_mem hc hd
      · intro c
        exact ((hHo (m + 1)).preimage (continuous_const.add continuous_id)).measurableSet
    have hc0 : (Fintype.card C : ENNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
    have hct : (Fintype.card C : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    apply (ENNReal.mul_right_inj hc0 hct).1
    calc (Fintype.card C : ENNReal) * (μ (hlev (Λ 0) (H (m + 1)) G y h) * ν (H 0))
        = μ (hlev (Λ 0) (H m) G y h) * ν (H 0) := by rw [hμ, mul_assoc]
      _ = μ (Λ 0) * ν (H m) := ih
      _ = (Fintype.card C : ENNReal) * (μ (Λ 0) * ν (H (m + 1))) := by rw [hν]; ring
end PI.VolStabS
