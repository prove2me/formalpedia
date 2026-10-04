-- Prove2me | solution 1 for StarShapedRisk.LawInvariant.theorem5_star_shaped_law_invariant_iff
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T06:53:21.641855+00:00
-- url     : https://prove2.me/submissions/c71fc635-bfdd-4307-8deb-4c7e6615c7ab

import Definitions.Def_StarShapedRisk_LawInvariant_Model
import Definitions.Def_StarShapedRisk_LawInvariant_VaR
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma lr_atomless_split_real (hP : IsAtomless P) (S : Set Ω) (hS : MeasurableSet S)
    (hpos : 0 < P.real S) : ∃ T ⊆ S, MeasurableSet T ∧
      0 < P.real T ∧ 0 < P.real (S \ T) ∧ P.real T + P.real (S \ T) = P.real S := by
  have hsp : 0 < P S := pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp hpos.ne')
  obtain ⟨T, hTS, hT, ht0, htS⟩ := hP S hS hsp
  have ht : 0 < P.real T := ENNReal.toReal_pos ht0.ne' (measure_ne_top _ _)
  have hlt : P.real T < P.real S := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr htS
  have he : P.real T + P.real (S \ T) = P.real S := by
    simpa [inter_eq_right.mpr hTS] using measureReal_inter_add_sdiff (μ := P) hT (s := S)
  exact ⟨T, hTS, hT, ht, by linarith, he⟩

lemma lr_atomless_small (hP : IsAtomless P) (S : Set Ω) (hS : MeasurableSet S)
    (hpos : 0 < P.real S) (ε : ℝ) (hε : 0 < ε) :
    ∃ T ⊆ S, MeasurableSet T ∧ 0 < P.real T ∧ P.real T < ε := by
  let V : Set ℝ := {r | ∃ T ⊆ S, MeasurableSet T ∧ 0 < P.real T ∧ r = P.real T}
  have hn : V.Nonempty := ⟨P.real S, S, subset_rfl, hS, hpos, rfl⟩
  have hb : BddBelow V := ⟨0, by rintro r ⟨T, hT, hm, hp, rfl⟩; exact hp.le⟩
  have h0 : 0 ≤ sInf V := le_csInf hn (by rintro r ⟨T, hT, hm, hp, rfl⟩; exact hp.le)
  have hz : sInf V = 0 := by
    apply le_antisymm ?_ h0
    by_contra h
    have hi : 0 < sInf V := lt_of_not_ge h
    obtain ⟨r, hr, hri⟩ := (csInf_lt_iff hb hn).mp (show sInf V < 2 * sInf V by linarith)
    rcases hr with ⟨T, hTS, hmT, hpT, rfl⟩
    obtain ⟨U, hUT, hmU, hpU, hpD, he⟩ := lr_atomless_split_real P hP T hmT hpT
    have hu : sInf V ≤ P.real U := csInf_le hb ⟨U, hUT.trans hTS, hmU, hpU, rfl⟩
    have hd : sInf V ≤ P.real (T \ U) :=
      csInf_le hb ⟨T \ U, sdiff_subset.trans hTS, hmT.diff hmU, hpD, rfl⟩
    linarith
  obtain ⟨r, hr, hre⟩ := (csInf_lt_iff hb hn).mp (by rw [hz]; exact hε)
  rcases hr with ⟨T, hTS, hmT, hpT, rfl⟩
  exact ⟨T, hTS, hmT, hpT, hre⟩
end StarShapedRisk.LawInvariant

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Classical MeasureTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

def lr_pack (S : Set Ω) (a : ℝ) (C : Set (Set Ω)) : Prop :=
  (∀ T ∈ C, T ⊆ S ∧ MeasurableSet T ∧ 0 < P T) ∧
  C.PairwiseDisjoint id ∧
  ∀ F : Finset (Set Ω), (↑F : Set (Set Ω)) ⊆ C → ∑ T ∈ F, P T ≤ ENNReal.ofReal a

def lr_pack_union (C : Set (Set Ω)) : Set Ω := ⋃ T : C, T.val

lemma lr_pack_union_subset (S : Set Ω) (a : ℝ) (C : Set (Set Ω)) (hC : lr_pack P S a C) :
    lr_pack_union C ⊆ S := by
  intro ω hω
  change ω ∈ ⋃ T : C, T.val at hω
  obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hω
  exact (hC.1 T.val T.property).1 hT

lemma lr_pack_countable (S : Set Ω) (a : ℝ) (C : Set (Set Ω)) (hC : lr_pack P S a C) :
    Countable C := by
  have hh := Measure.countable_meas_pos_of_disjoint_iUnion (μ := P)
    (fun T : C => (hC.1 T T.property).2.1)
    (show Pairwise (fun T V : C => Disjoint T.val V.val) by
      intro T V hne
      exact hC.2.1 T.property V.property (by intro he; exact hne (Subtype.ext he)))
  have he : {T : C | 0 < P T.val} = univ := by ext T; simp [(hC.1 T T.property).2.2]
  rw [he] at hh
  exact Set.countable_univ_iff.mp hh

lemma lr_pack_union_bound (S : Set Ω) (a : ℝ) (C : Set (Set Ω)) (hC : lr_pack P S a C) :
    MeasurableSet (lr_pack_union C) ∧ P (lr_pack_union C) ≤ ENNReal.ofReal a := by
  haveI : Countable C := lr_pack_countable P S a C hC
  refine ⟨MeasurableSet.iUnion (fun T : C => (hC.1 T T.property).2.1), ?_⟩
  rw [lr_pack_union, measure_iUnion]
  · apply ENNReal.summable.tsum_le_of_sum_le
    intro F
    have hh := hC.2.2 (F.map ⟨Subtype.val, Subtype.val_injective⟩) (by
      intro T hT
      rcases Finset.mem_map.mp hT with ⟨V, hV, rfl⟩
      exact V.property)
    simpa only [Finset.sum_map, Function.Embedding.coeFn_mk] using hh
  · intro T V hne
    exact hC.2.1 T.property V.property (by intro he; exact hne (Subtype.ext he))
  · exact fun T : C => (hC.1 T T.property).2.1

lemma lr_atomless_division (hP : IsAtomless P) (S : Set Ω) (hS : MeasurableSet S)
    (a : ℝ) (ha0 : 0 ≤ a) (haS : a ≤ P.real S) :
    ∃ T ⊆ S, MeasurableSet T ∧ P.real T = a := by
  let V : Set (Set (Set Ω)) := {C | lr_pack P S a C}
  have hEmpty : (∅ : Set (Set Ω)) ∈ V := by
    refine ⟨by simp, by simp, ?_⟩
    intro F hF
    have he : F = ∅ := Finset.coe_injective (by simpa using Set.Subset.antisymm hF (empty_subset _))
    simp [he]
  have hZ : ∀ c ⊆ V, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ V, ∀ C ∈ c, C ⊆ ub := by
    intro c hc hchain hne
    refine ⟨sUnion c, ?_, fun C hC => subset_sUnion_of_mem hC⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro T ⟨C, hCc, hTC⟩
      exact (hc hCc).1 T hTC
    · rintro T ⟨C, hCc, hTC⟩ U ⟨D, hDc, hUD⟩ hTU
      rcases hchain.total hCc hDc with hCD | hDC
      · exact (hc hDc).2.1 (hCD hTC) hUD hTU
      · exact (hc hCc).2.1 hTC (hDC hUD) hTU
    · have hcover : ∀ F : Finset (Set Ω), (↑F : Set (Set Ω)) ⊆ sUnion c →
          ∃ C ∈ c, (↑F : Set (Set Ω)) ⊆ C := by
        intro F
        induction F using Finset.induction_on with
        | empty =>
          intro _
          obtain ⟨C, hC⟩ := hne
          exact ⟨C, hC, by simp⟩
        | @insert T F hTF ih =>
          intro hF
          obtain ⟨C, hCc, hTC⟩ := hF (Finset.mem_insert_self T F)
          obtain ⟨D, hDc, hFD⟩ := ih (fun U hU => hF (Finset.mem_insert_of_mem hU))
          rcases hchain.total hCc hDc with hCD | hDC
          · exact ⟨D, hDc, by intro U hU; rcases Finset.mem_insert.mp hU with rfl | hU; exact hCD hTC; exact hFD hU⟩
          · exact ⟨C, hCc, by intro U hU; rcases Finset.mem_insert.mp hU with rfl | hU; exact hTC; exact hDC (hFD hU)⟩
      intro F hF
      obtain ⟨C, hCc, hFC⟩ := hcover F hF
      exact (hc hCc).2.2 F hFC
  obtain ⟨C, _, hmax⟩ := zorn_subset_nonempty V hZ ∅ hEmpty
  have hC : lr_pack P S a C := hmax.1
  let U := lr_pack_union C
  have hUS : U ⊆ S := lr_pack_union_subset P S a C hC
  obtain ⟨hmU, hbU⟩ := lr_pack_union_bound P S a C hC
  change MeasurableSet U at hmU
  change P U ≤ ENNReal.ofReal a at hbU
  have hu : P.real U ≤ a := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbU
    simpa [measureReal_def, ENNReal.toReal_ofReal ha0] using hh
  refine ⟨U, hUS, hmU, le_antisymm hu ?_⟩
  by_contra h
  have hlt : P.real U < a := lt_of_not_ge h
  have he : P.real U + P.real (S \ U) = P.real S := by
    simpa [inter_eq_right.mpr hUS] using measureReal_inter_add_sdiff (μ := P) hmU (s := S)
  have hpD : 0 < P.real (S \ U) := by linarith
  obtain ⟨T, hTD, hmT, hpT, htδ⟩ := lr_atomless_small P hP (S \ U) (hS.diff hmU) hpD (a-P.real U) (by linarith)
  have hTU : Disjoint T U := disjoint_left.mpr (fun ω hT hU => (hTD hT).2 hU)
  have htP : 0 < P T := pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp hpT.ne')
  have hnewM : P (T ∪ U) ≤ ENNReal.ofReal a := by
    have hh : P.real (T ∪ U) ≤ a := by rw [measureReal_union hTU hmU]; linarith
    have hz := ENNReal.ofReal_le_ofReal hh
    simpa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)] using hz
  have hnew : insert T C ∈ V := by
    refine ⟨?_, ?_, ?_⟩
    · intro A hA
      rcases hA with rfl | hA
      · exact ⟨hTD.trans sdiff_subset, hmT, htP⟩
      · exact hC.1 A hA
    · intro A hA B hB hAB
      rcases hA with rfl | hA <;> rcases hB with rfl | hB
      · exact (hAB rfl).elim
      · exact hTU.mono_right (subset_iUnion_of_subset ⟨B,hB⟩ subset_rfl)
      · exact (hTU.mono_right (subset_iUnion_of_subset ⟨A,hA⟩ subset_rfl)).symm
      · exact hC.2.1 hA hB hAB
    · intro F hF
      have hd : (↑F : Set (Set Ω)).PairwiseDisjoint id := by
        intro A hA B hB hAB
        rcases hF hA with rfl | hA <;> rcases hF hB with rfl | hB
        · exact (hAB rfl).elim
        · exact hTU.mono_right (subset_iUnion_of_subset ⟨B,hB⟩ subset_rfl)
        · exact (hTU.mono_right (subset_iUnion_of_subset ⟨A,hA⟩ subset_rfl)).symm
        · exact hC.2.1 hA hB hAB
      have hf := measure_biUnion_finset (μ := P) hd (fun A hA => by
        rcases hF hA with rfl | hA; exact hmT; exact (hC.1 A hA).2.1)
      simp only [id_eq] at hf
      rw [← hf]
      apply le_trans (measure_mono ?_) hnewM
      intro ω hω
      obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hω
      obtain ⟨hAF, hω⟩ := Set.mem_iUnion.mp hA
      rcases hF hAF with rfl | hAC
      · exact Or.inl hω
      · exact Or.inr (mem_iUnion.mpr ⟨⟨A,hAC⟩,hω⟩)
  have hTC : T ∈ C := (hmax.2 hnew (subset_insert T C)) (mem_insert T C)
  have hTe : T = ∅ := by
    apply Set.Subset.antisymm ?_ (empty_subset _)
    intro ω hω
    exact (hTD hω).2 (mem_iUnion.mpr ⟨⟨T,hTC⟩,hω⟩)
  simpa [hTe] using htP
end StarShapedRisk.LawInvariant

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Classical MeasureTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

structure LrCutSystem (C : Set (ℚ × Set Ω)) : Prop where
  zero_mem : (0, ∅) ∈ C
  one_mem : (1, univ) ∈ C
  valid : ∀ p ∈ C, 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ MeasurableSet p.2 ∧
    P.real p.2 = (p.1 : ℝ)
  ordered : ∀ p ∈ C, ∀ r ∈ C, p.1 ≤ r.1 → p.2 ⊆ r.2

lemma lr_cut_countable (C : Set (ℚ × Set Ω)) (hC : LrCutSystem P C) : Countable C := by
  apply Function.Injective.countable (f := fun p : C => p.val.1)
  intro p r he
  apply Subtype.ext
  apply Prod.ext he
  exact Set.Subset.antisymm
    (hC.ordered p p.property r r.property he.le)
    (hC.ordered r r.property p p.property he.symm.le)

lemma lr_directed_union_real_le {ι : Type*} [Countable ι] (s : ι → Set Ω)
    (hd : Directed (· ⊆ ·) s) (r : ℝ) (hr : 0 ≤ r)
    (hb : ∀ i, P.real (s i) ≤ r) : P.real (⋃ i, s i) ≤ r := by
  have he : P (⋃ i, s i) ≤ ENNReal.ofReal r := by
    rw [hd.measure_iUnion]
    apply iSup_le
    intro i
    have hh := ENNReal.ofReal_le_ofReal (hb i)
    simpa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)] using hh
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa [measureReal_def, ENNReal.toReal_ofReal hr] using hh

lemma lr_cut_extend (hP : IsAtomless P) (C : Set (ℚ × Set Ω))
    (hC : LrCutSystem P C) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ T : Set Ω, LrCutSystem P (insert (q,T) C) := by
  haveI : Countable C := lr_cut_countable P C hC
  let I := {p : C // p.val.1 ≤ q}
  let J := {p : C // q ≤ p.val.1}
  let L : Set Ω := ⋃ p : I, p.val.val.2
  let R : Set Ω := ⋂ p : J, p.val.val.2
  have hmL : MeasurableSet L := MeasurableSet.iUnion
    (fun p : I => (hC.valid p.val.val p.val.property).2.2.1)
  have hmR : MeasurableSet R := MeasurableSet.iInter
    (fun p : J => (hC.valid p.val.val p.val.property).2.2.1)
  have hLR : L ⊆ R := by
    intro ω hω
    obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hω
    apply Set.mem_iInter.mpr
    intro r
    exact hC.ordered p.val.val p.val.property r.val.val r.val.property
      (p.property.trans r.property) hp
  have hdL : Directed (· ⊆ ·) (fun p : I => p.val.val.2) := by
    intro p r
    rcases le_total p.val.val.1 r.val.val.1 with h | h
    · exact ⟨r, hC.ordered p.val.val p.val.property r.val.val r.val.property h, subset_rfl⟩
    · exact ⟨p, subset_rfl, hC.ordered r.val.val r.val.property p.val.val p.val.property h⟩
  have hq0r : (0:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq0
  have hq1r : (q:ℝ) ≤ 1 := by exact_mod_cast hq1
  have hL : P.real L ≤ (q:ℝ) := lr_directed_union_real_le P _ hdL _ hq0r (by
    intro p
    rw [(hC.valid p.val.val p.val.property).2.2.2]
    exact_mod_cast p.property)
  have hdc : Directed (· ⊆ ·) (fun p : J => p.val.val.2ᶜ) := by
    intro p r
    rcases le_total p.val.val.1 r.val.val.1 with h | h
    · exact ⟨p, subset_rfl, compl_subset_compl.mpr
        (hC.ordered p.val.val p.val.property r.val.val r.val.property h)⟩
    · exact ⟨r, compl_subset_compl.mpr
        (hC.ordered r.val.val r.val.property p.val.val p.val.property h), subset_rfl⟩
  have hc : P.real (⋃ p : J, p.val.val.2ᶜ) ≤ 1-(q:ℝ) :=
    lr_directed_union_real_le P _ hdc _ (by linarith) (by
      intro p
      rw [measureReal_compl (hC.valid p.val.val p.val.property).2.2.1,
        probReal_univ, (hC.valid p.val.val p.val.property).2.2.2]
      have hh : (q:ℝ) ≤ (p.val.val.1:ℝ) := by exact_mod_cast p.property
      linarith)
  have hR : (q:ℝ) ≤ P.real R := by
    have he : Rᶜ = ⋃ p : J, p.val.val.2ᶜ := compl_iInter _
    rw [← he, measureReal_compl hmR, probReal_univ] at hc
    linarith
  have he : P.real L + P.real (R \ L) = P.real R := by
    simpa only [inter_eq_right.mpr hLR] using measureReal_inter_add_sdiff (μ := P) hmL (s := R)
  obtain ⟨T, hT, hmT, ht⟩ := lr_atomless_division P hP (R \ L) (hmR.diff hmL)
    ((q:ℝ)-P.real L) (by linarith) (by linarith)
  have hdTL : Disjoint T L := disjoint_left.mpr (fun ω hω hωL => (hT hω).2 hωL)
  have hnew : P.real (L ∪ T) = (q:ℝ) := by
    rw [measureReal_union hdTL.symm hmT, ht]; ring
  have hnewR : L ∪ T ⊆ R := union_subset hLR (hT.trans sdiff_subset)
  have hlow : ∀ p ∈ C, p.1 ≤ q → p.2 ⊆ L ∪ T := by
    intro p hp hpq ω hω
    exact Or.inl (Set.mem_iUnion.mpr ⟨⟨⟨p,hp⟩,hpq⟩,hω⟩)
  have hupp : ∀ p ∈ C, q ≤ p.1 → L ∪ T ⊆ p.2 := by
    intro p hp hqp
    exact hnewR.trans (Set.iInter_subset (fun p : J => p.val.val.2) ⟨⟨p,hp⟩,hqp⟩)
  refine ⟨L ∪ T, ?_⟩
  refine ⟨mem_insert_of_mem _ hC.zero_mem, mem_insert_of_mem _ hC.one_mem, ?_, ?_⟩
  · intro p hp
    rcases hp with rfl | hp
    · exact ⟨hq0,hq1,hmL.union hmT,hnew⟩
    · exact hC.valid p hp
  · intro p hp r hr hpr
    rcases hp with rfl | hp <;> rcases hr with rfl | hr
    · exact subset_rfl
    · exact hupp r hr hpr
    · exact hlow p hp hpr
    · exact hC.ordered p hp r hr hpr

lemma lr_atomless_rational_cuts (hP : IsAtomless P) :
    ∃ B : Icc (0:ℚ) 1 → Set Ω,
      (∀ q, MeasurableSet (B q) ∧ P.real (B q) = (q.val:ℝ)) ∧
      Monotone B ∧ B ⟨0,by norm_num⟩ = ∅ ∧ B ⟨1,by norm_num⟩ = univ := by
  let V : Set (Set (ℚ × Set Ω)) := {C | LrCutSystem P C}
  let C₀ : Set (ℚ × Set Ω) := {(0,∅),(1,univ)}
  have h₀ : C₀ ∈ V := by
    refine ⟨by simp [C₀], by simp [C₀], ?_, ?_⟩
    · intro p hp
      rcases hp with rfl | rfl
      · simp
      · simp
    · intro p hp r hr hpr
      rcases hp with rfl | rfl <;> rcases hr with rfl | rfl <;> simp_all
      norm_num at hpr
  have hZ : ∀ c ⊆ V, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ V, ∀ C ∈ c, C ⊆ ub := by
    intro c hc hchain hne
    obtain ⟨D,hD⟩ := hne
    refine ⟨sUnion c, ?_, fun C hC => subset_sUnion_of_mem hC⟩
    refine ⟨mem_sUnion.mpr ⟨D,hD,(hc hD).zero_mem⟩,
      mem_sUnion.mpr ⟨D,hD,(hc hD).one_mem⟩, ?_, ?_⟩
    · rintro p ⟨C,hCc,hpC⟩
      exact (hc hCc).valid p hpC
    · rintro p ⟨C,hCc,hpC⟩ r ⟨D,hDc,hrD⟩ hpr
      rcases hchain.total hCc hDc with hCD | hDC
      · exact (hc hDc).ordered p (hCD hpC) r hrD hpr
      · exact (hc hCc).ordered p hpC r (hDC hrD) hpr
  obtain ⟨C,_,hmax⟩ := zorn_subset_nonempty V hZ C₀ h₀
  have hC : LrCutSystem P C := hmax.1
  have htotal : ∀ q : Icc (0:ℚ) 1, ∃ T : Set Ω, (q.val,T) ∈ C := by
    intro q
    obtain ⟨T,hT⟩ := lr_cut_extend P hP C hC q.val q.property.1 q.property.2
    exact ⟨T, (hmax.2 hT (subset_insert _ _)) (mem_insert _ _)⟩
  choose B hB using htotal
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro q
    exact ⟨(hC.valid _ (hB q)).2.2.1,(hC.valid _ (hB q)).2.2.2⟩
  · intro q r hqr
    exact hC.ordered _ (hB q) _ (hB r) hqr
  · apply Set.Subset.antisymm ?_ (empty_subset _)
    exact hC.ordered _ (hB _) _ hC.zero_mem le_rfl
  · apply Set.Subset.antisymm (subset_univ _) ?_
    exact hC.ordered _ hC.one_mem _ (hB _) le_rfl

end StarShapedRisk.LawInvariant

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Classical MeasureTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

noncomputable def lr_cut_variable (B : Icc (0:ℚ) 1 → Set Ω) (ω : Ω) : ℝ :=
  sInf {r : ℝ | ∃ q : Icc (0:ℚ) 1, ω ∈ B q ∧ r = (q.val:ℝ)}

lemma lr_cut_variable_bounds (B : Icc (0:ℚ) 1 → Set Ω)
    (h1 : B ⟨1,by norm_num⟩ = univ) (ω : Ω) :
    (0:ℝ) ≤ lr_cut_variable B ω ∧ lr_cut_variable B ω ≤ 1 := by
  have hn : {r : ℝ | ∃ q : Icc (0:ℚ) 1, ω ∈ B q ∧ r = (q.val:ℝ)}.Nonempty :=
    ⟨1, ⟨1,by norm_num⟩, by rw [h1]; trivial, by simp⟩
  have hl : ∀ r ∈ {r : ℝ | ∃ q : Icc (0:ℚ) 1, ω ∈ B q ∧ r = (q.val:ℝ)}, 0 ≤ r := by
    rintro r ⟨q,_,rfl⟩
    exact_mod_cast q.property.1
  exact ⟨le_csInf hn hl, csInf_le ⟨0,hl⟩ ⟨⟨1,by norm_num⟩, by rw [h1]; trivial, by simp⟩⟩

lemma lr_cut_variable_lt (B : Icc (0:ℚ) 1 → Set Ω)
    (h1 : B ⟨1,by norm_num⟩ = univ) (ω : Ω) (t : ℝ) :
    lr_cut_variable B ω < t ↔ ∃ q : Icc (0:ℚ) 1, ω ∈ B q ∧ (q.val:ℝ) < t := by
  have hn : {r : ℝ | ∃ q : Icc (0:ℚ) 1, ω ∈ B q ∧ r = (q.val:ℝ)}.Nonempty :=
    ⟨1, ⟨1,by norm_num⟩, by rw [h1]; trivial, by simp⟩
  have hb : BddBelow {r : ℝ | ∃ q : Icc (0:ℚ) 1, ω ∈ B q ∧ r = (q.val:ℝ)} := by
    refine ⟨0,?_⟩
    rintro r ⟨q,_,rfl⟩
    exact_mod_cast q.property.1
  rw [lr_cut_variable, csInf_lt_iff hb hn]
  constructor
  · rintro ⟨r,⟨q,hq,rfl⟩,hrt⟩
    exact ⟨q,hq,hrt⟩
  · rintro ⟨q,hq,hqt⟩
    exact ⟨q.val,⟨q,hq,rfl⟩,hqt⟩

lemma lr_cut_variable_measurable (B : Icc (0:ℚ) 1 → Set Ω)
    (hm : ∀ q, MeasurableSet (B q)) (h1 : B ⟨1,by norm_num⟩ = univ) :
    Measurable (lr_cut_variable B) := by
  apply measurable_of_Iio
  intro t
  have he : lr_cut_variable B ⁻¹' Iio t = ⋃ q : {q : Icc (0:ℚ) 1 // (q.val:ℝ) < t}, B q.val := by
    ext ω
    simp only [mem_preimage, mem_Iio, lr_cut_variable_lt B h1, mem_iUnion]
    constructor
    · rintro ⟨q,hq,hqt⟩
      exact ⟨⟨q,hqt⟩,hq⟩
    · rintro ⟨q,hq⟩
      exact ⟨q.val,hq,q.property⟩
  rw [he]
  exact MeasurableSet.iUnion (fun q => hm q.val)

lemma lr_cut_variable_cdf (B : Icc (0:ℚ) 1 → Set Ω)
    (hm : ∀ q, MeasurableSet (B q)) (hB : ∀ q, P.real (B q) = (q.val:ℝ))
    (hmono : Monotone B) (h1 : B ⟨1,by norm_num⟩ = univ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.real {ω | lr_cut_variable B ω ≤ t} = t := by
  let E : Set Ω := {ω | lr_cut_variable B ω ≤ t}
  have hp0 : 0 ≤ P.real E := measureReal_nonneg
  have hp1 : P.real E ≤ 1 := measureReal_le_one
  apply le_antisymm
  · by_contra h
    have hlt : t < P.real E := lt_of_not_ge h
    obtain ⟨q,htq,hqE⟩ := exists_rat_btwn hlt
    have hq0 : (0:ℚ) ≤ q := by exact_mod_cast (ht0.trans htq.le)
    have hq1 : q ≤ (1:ℚ) := by exact_mod_cast (hqE.le.trans hp1)
    let qr : Icc (0:ℚ) 1 := ⟨q,hq0,hq1⟩
    have hsub : E ⊆ B qr := by
      intro ω hω
      obtain ⟨r,hr,hrq⟩ := (lr_cut_variable_lt B h1 ω q).mp (hω.trans_lt htq)
      have hrqr : r ≤ qr := by change r.val ≤ q; exact_mod_cast hrq.le
      exact hmono hrqr hr
    have hh := measureReal_mono (μ := P) hsub
    rw [hB qr] at hh
    exact (not_le_of_gt hqE) hh
  · by_contra h
    have hlt : P.real E < t := lt_of_not_ge h
    obtain ⟨q,hEq,hqt⟩ := exists_rat_btwn hlt
    have hq0 : (0:ℚ) ≤ q := by exact_mod_cast (hp0.trans hEq.le)
    have hq1 : q ≤ (1:ℚ) := by exact_mod_cast (hqt.le.trans ht1)
    let qr : Icc (0:ℚ) 1 := ⟨q,hq0,hq1⟩
    have hsub : B qr ⊆ E := by
      intro ω hω
      exact ((lr_cut_variable_lt B h1 ω t).mpr ⟨qr,hω,hqt⟩).le
    have hh := measureReal_mono (μ := P) hsub
    rw [hB qr] at hh
    exact (not_le_of_gt hEq) hh

lemma lr_cut_variable_strict_cdf (B : Icc (0:ℚ) 1 → Set Ω)
    (hm : ∀ q, MeasurableSet (B q)) (hB : ∀ q, P.real (B q) = (q.val:ℝ))
    (hmono : Monotone B) (h1 : B ⟨1,by norm_num⟩ = univ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.real {ω | lr_cut_variable B ω < t} = t := by
  let E : Set Ω := {ω | lr_cut_variable B ω < t}
  have hsub : {ω | lr_cut_variable B ω < t} ⊆ {ω | lr_cut_variable B ω ≤ t} := by
    intro ω hω
    change lr_cut_variable B ω < t at hω
    change lr_cut_variable B ω ≤ t
    exact hω.le
  apply le_antisymm
  · exact (measureReal_mono (μ := P) hsub).trans
      (lr_cut_variable_cdf P B hm hB hmono h1 t ht0 ht1).le
  · by_contra h
    have hlt : P.real E < t := lt_of_not_ge h
    obtain ⟨q,hEq,hqt⟩ := exists_rat_btwn hlt
    have hq0 : (0:ℚ) ≤ q := by exact_mod_cast ((measureReal_nonneg (μ := P) (s := E)).trans hEq.le)
    have hq1 : q ≤ (1:ℚ) := by exact_mod_cast (hqt.le.trans ht1)
    let qr : Icc (0:ℚ) 1 := ⟨q,hq0,hq1⟩
    have hsub : B qr ⊆ E := by
      intro ω hω
      exact (lr_cut_variable_lt B h1 ω t).mpr ⟨qr,hω,hqt⟩
    have hh := measureReal_mono (μ := P) hsub
    rw [hB qr] at hh
    exact (not_le_of_gt hEq) hh

lemma lr_atomless_uniform (hP : IsAtomless P) :
    ∃ U : Ω → ℝ, Measurable U ∧ (∀ ω, U ω ∈ Icc (0:ℝ) 1) ∧
      (∀ t ∈ Icc (0:ℝ) 1, P.real {ω | U ω ≤ t} = t) ∧
      P.real {ω | U ω < 1} = 1 := by
  obtain ⟨B,hm,hmono,_,h1⟩ := lr_atomless_rational_cuts P hP
  refine ⟨lr_cut_variable B, lr_cut_variable_measurable B (fun q => (hm q).1) h1,
    fun ω => lr_cut_variable_bounds B h1 ω, ?_, ?_⟩
  · intro t ht
    exact lr_cut_variable_cdf P B (fun q => (hm q).1) (fun q => (hm q).2) hmono h1 t ht.1 ht.2
  · exact lr_cut_variable_strict_cdf P B (fun q => (hm q).1) (fun q => (hm q).2)
      hmono h1 1 (by norm_num) le_rfl

end StarShapedRisk.LawInvariant

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma lr_cdf_prob (X : Positions Ω) (t : ℝ) :
    ENNReal.ofReal (cdf (P.map X.val) t) = P {ω | X.val ω ≤ t} := by
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  rw [ofReal_cdf, Measure.map_apply X.property.1 measurableSet_Iic]
  rfl

lemma lr_threshold (X : Positions Ω) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    P {ω | t < X.val ω} ≤ ENNReal.ofReal (1-α) ↔ α ≤ cdf (P.map X.val) t := by
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  have hm : MeasurableSet {ω | X.val ω ≤ t} := measurableSet_le X.property.1 measurable_const
  have he : {ω | t < X.val ω} = {ω | X.val ω ≤ t}ᶜ := by ext ω; simp
  rw [he, measure_compl hm (measure_ne_top _ _), measure_univ, ← lr_cdf_prob P X t]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (cdf_nonneg _ _), ENNReal.ofReal_le_ofReal_iff (by linarith [hα.2])]
  constructor <;> intro h <;> linarith

lemma lr_quantile_bounds (X : Positions Ω) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) :
    {t : ℝ | α ≤ cdf (P.map X.val) t}.Nonempty ∧
      BddBelow {t : ℝ | α ≤ cdf (P.map X.val) t} := by
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  obtain ⟨C,hC⟩ := X.property.2
  have hc : cdf (P.map X.val) C = 1 := by
    have he : {ω | X.val ω ≤ C} = univ := by ext ω; simp [(abs_le.mp (hC ω)).2]
    have hh := lr_cdf_prob P X C
    rw [he, measure_univ] at hh
    exact ENNReal.ofReal_eq_one.mp hh
  refine ⟨⟨C, hα.2.le.trans_eq hc.symm⟩, -C, ?_⟩
  intro t ht
  by_contra h
  have hlt : t < -C := lt_of_not_ge h
  have he : {ω | X.val ω ≤ t} = ∅ := by
    ext ω; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    linarith [(abs_le.mp (hC ω)).1]
  have hh := lr_cdf_prob P X t
  rw [he, measure_empty] at hh
  have hz : cdf (P.map X.val) t = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hh) (cdf_nonneg _ _)
  change α ≤ cdf (P.map X.val) t at ht
  rw [hz] at ht
  exact (not_le_of_gt hα.1) ht

lemma lr_quantile_le (X : Positions Ω) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    VaR P α X.val ≤ t ↔ α ≤ cdf (P.map X.val) t := by
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  have he : {r : ℝ | P {ω | r < X.val ω} ≤ ENNReal.ofReal (1-α)} =
      {r : ℝ | α ≤ cdf (P.map X.val) r} := by ext r; exact lr_threshold P X α hα r
  have hb := lr_quantile_bounds P X α hα
  let q := sInf {r : ℝ | α ≤ cdf (P.map X.val) r}
  have hq : α ≤ cdf (P.map X.val) q := by
    have hc := ((cdf (P.map X.val)).right_continuous q).mono Ioi_subset_Ici_self
    apply ge_of_tendsto hc
    filter_upwards [self_mem_nhdsWithin] with r hr
    obtain ⟨s, hs, hsr⟩ := (csInf_lt_iff hb.2 hb.1).mp hr
    exact hs.trans ((cdf (P.map X.val)).mono hsr.le)
  change sInf _ ≤ t ↔ _
  rw [he]
  constructor
  · intro h; exact hq.trans ((cdf (P.map X.val)).mono h)
  · intro h; exact csInf_le hb.2 h
end StarShapedRisk.LawInvariant

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma lr_cdf_shift (X : Positions Ω) (m u : ℝ) :
    cdf (P.map (X - const m).val) u = cdf (P.map X.val) (u+m) := by
  have h1 := lr_cdf_prob P (X-const m) u
  have h2 := lr_cdf_prob P X (u+m)
  have he : {ω | (X-const m).val ω ≤ u} = {ω | X.val ω ≤ u+m} := by
    ext ω; change X.val ω - m ≤ u ↔ X.val ω ≤ u+m; constructor <;> intro h <;> linarith
  rw [he, ← h2] at h1
  have hh := congrArg ENNReal.toReal h1
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  haveI : IsProbabilityMeasure (P.map (X-const m).val) := Measure.isProbabilityMeasure_map (X-const m).property.1.aemeasurable
  simpa [cdf_nonneg] using hh

lemma lr_var_cash (X : Positions Ω) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (m : ℝ) :
    VaR P α (X-const m).val = VaR P α X.val - m := by
  apply le_antisymm
  · apply (lr_quantile_le P (X-const m) α hα _).mpr
    rw [lr_cdf_shift]
    simpa using (lr_quantile_le P X α hα (VaR P α X.val)).mp le_rfl
  · have hh := (lr_quantile_le P (X-const m) α hα (VaR P α (X-const m).val)).mp le_rfl
    rw [lr_cdf_shift] at hh
    have hv := (lr_quantile_le P X α hα _).mpr hh
    linarith

lemma lr_cdf_scale (X : Positions Ω) (t : ℝ) (ht : 0 < t) (u : ℝ) :
    cdf (P.map (t • X).val) u = cdf (P.map X.val) (u/t) := by
  have h1 := lr_cdf_prob P (t • X) u
  have h2 := lr_cdf_prob P X (u/t)
  have he : {ω | (t • X).val ω ≤ u} = {ω | X.val ω ≤ u/t} := by
    ext ω; change t * X.val ω ≤ u ↔ X.val ω ≤ u/t
    rw [le_div_iff₀ ht, mul_comm]
  rw [he, ← h2] at h1
  have hh := congrArg ENNReal.toReal h1
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  haveI : IsProbabilityMeasure (P.map (t • X).val) := Measure.isProbabilityMeasure_map (t • X).property.1.aemeasurable
  simpa [cdf_nonneg] using hh

lemma lr_var_scale (X : Positions Ω) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (t : ℝ) (ht : 0 < t) : VaR P α (t • X).val = t * VaR P α X.val := by
  apply le_antisymm
  · apply (lr_quantile_le P (t • X) α hα _).mpr
    rw [lr_cdf_scale P X t ht]
    rw [mul_div_cancel_left₀ _ ht.ne']
    exact (lr_quantile_le P X α hα (VaR P α X.val)).mp le_rfl
  · have hh := (lr_quantile_le P (t • X) α hα (VaR P α (t • X).val)).mp le_rfl
    rw [lr_cdf_scale P X t ht] at hh
    have hv := (lr_quantile_le P X α hα _).mpr hh
    nlinarith [(le_div_iff₀ ht).mp hv]

lemma lr_var_monotone_loss (X Y : Positions Ω) (hXY : ∀ ω, X.val ω ≤ Y.val ω)
    (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) : VaR P α X.val ≤ VaR P α Y.val := by
  apply (lr_quantile_le P X α hα _).mpr
  have hy := (lr_quantile_le P Y α hα (VaR P α Y.val)).mp le_rfl
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y.val) := Measure.isProbabilityMeasure_map Y.property.1.aemeasurable
  have hc : cdf (P.map Y.val) (VaR P α Y.val) ≤ cdf (P.map X.val) (VaR P α Y.val) := by
    apply (ENNReal.ofReal_le_ofReal_iff (cdf_nonneg _ _)).mp
    rw [lr_cdf_prob, lr_cdf_prob]
    exact measure_mono (fun ω hω => (hXY ω).trans hω)
  exact hy.trans hc

lemma lr_var_monotone_level (X : Positions Ω) :
    Monotone (fun α : Ioo (0 : ℝ) 1 => VaR P α.val X.val) := by
  intro α β hαβ
  change α.val ≤ β.val at hαβ
  apply (lr_quantile_le P X α.val α.property _).mpr
  exact hαβ.trans ((lr_quantile_le P X β.val β.property (VaR P β.val X.val)).mp le_rfl)

lemma lr_var_measurable_level (X : Positions Ω) :
    Measurable (fun α : Ioo (0 : ℝ) 1 => VaR P α.val X.val) :=
  (lr_var_monotone_level P X).measurable

lemma lr_var_law_invariant (X Y : Positions Ω) (hLaw : P.map X.val = P.map Y.val)
    (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) : VaR P α X.val = VaR P α Y.val := by
  apply le_antisymm
  · apply (lr_quantile_le P X α hα _).mpr
    rw [hLaw]
    exact (lr_quantile_le P Y α hα (VaR P α Y.val)).mp le_rfl
  · apply (lr_quantile_le P Y α hα _).mpr
    rw [← hLaw]
    exact (lr_quantile_le P X α hα (VaR P α X.val)).mp le_rfl
lemma lr_var_const (m : ℝ) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) :
    VaR P α (const (Ω := Ω) m).val = m := by
  haveI : IsProbabilityMeasure (P.map (const (Ω := Ω) m).val) :=
    Measure.isProbabilityMeasure_map (const m).property.1.aemeasurable
  have hc : cdf (P.map (const (Ω := Ω) m).val) m = 1 := by
    have hh := lr_cdf_prob P (const m) m
    have he : {ω : Ω | (const m).val ω ≤ m} = univ := by ext ω; simp [const]
    rw [he, measure_univ] at hh
    exact ENNReal.ofReal_eq_one.mp hh
  apply le_antisymm
  · exact (lr_quantile_le P (const m) α hα m).mpr (hα.2.le.trans_eq hc.symm)
  · by_contra h
    have hlt : VaR P α (const (Ω := Ω) m).val < m := lt_of_not_ge h
    have he : {ω : Ω | (const m).val ω ≤ VaR P α (const (Ω := Ω) m).val} = ∅ := by
      ext ω
      change m ≤ VaR P α (const (Ω := Ω) m).val ↔ False
      exact iff_false_intro (not_le_of_gt hlt)
    have hh := lr_cdf_prob P (const m) (VaR P α (const (Ω := Ω) m).val)
    rw [he, measure_empty] at hh
    have hz : cdf (P.map (const (Ω := Ω) m).val) (VaR P α (const (Ω := Ω) m).val) = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp hh) (cdf_nonneg _ _)
    have hq := (lr_quantile_le P (const m) α hα (VaR P α (const (Ω := Ω) m).val)).mp le_rfl
    rw [hz] at hq
    exact (not_le_of_gt hα.1) hq

lemma lr_var_bounded (X : Positions Ω) (C : ℝ) (hC : ∀ ω, |X.val ω| ≤ C)
    (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) : -C ≤ VaR P α X.val ∧ VaR P α X.val ≤ C := by
  have hl := lr_var_monotone_loss P (const (-C)) X (fun ω => (abs_le.mp (hC ω)).1) α hα
  have hu := lr_var_monotone_loss P X (const C) (fun ω => (abs_le.mp (hC ω)).2) α hα
  rw [lr_var_const P (-C) α hα] at hl
  rw [lr_var_const P C α hα] at hu
  exact ⟨hl, hu⟩

end StarShapedRisk.LawInvariant


set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant

open MeasureTheory

/-- Castagnoli et al. (2022), Eq. (A.1) (p. 2652): for bounded measurable losses `X`, `Y` on a
probability space, `F_X ≥ F_Y` pointwise if and only if `VaR_α(X) ≤ VaR_α(Y)` for all
`α ∈ (0,1)`. No atomlessness is assumed. -/
theorem eqA1_fsd_iff_VaR_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Positions Ω) :
    FSD P X.1 Y.1 ↔ ∀ α ∈ Set.Ioo (0 : ℝ) 1, VaR P α X.1 ≤ VaR P α Y.1 := by
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y.val) := Measure.isProbabilityMeasure_map Y.property.1.aemeasurable
  constructor
  · intro h α hα
    apply (lr_quantile_le P X α hα _).mpr
    have hy := (lr_quantile_le P Y α hα (VaR P α Y.val)).mp le_rfl
    have hc : cdf (P.map Y.val) (VaR P α Y.val) ≤ cdf (P.map X.val) (VaR P α Y.val) := by
      apply (ENNReal.ofReal_le_ofReal_iff (cdf_nonneg _ _)).mp
      rw [lr_cdf_prob, lr_cdf_prob]
      exact h _
    exact hy.trans hc
  · intro h t
    rw [← lr_cdf_prob P Y t, ← lr_cdf_prob P X t]
    apply ENNReal.ofReal_le_ofReal
    by_contra hn
    have hlt : cdf (P.map X.val) t < cdf (P.map Y.val) t := lt_of_not_ge hn
    let α := (cdf (P.map X.val) t + cdf (P.map Y.val) t) / 2
    have hα0 : 0 < α := by dsimp [α]; linarith [cdf_nonneg (P.map X.val) t]
    have hα1 : α < 1 := by dsimp [α]; linarith [cdf_le_one (P.map Y.val) t]
    have hy : VaR P α Y.val ≤ t := (lr_quantile_le P Y α ⟨hα0,hα1⟩ t).mpr (by dsimp [α]; linarith)
    have hx := (lr_quantile_le P X α ⟨hα0,hα1⟩ t).mp ((h α ⟨hα0,hα1⟩).trans hy)
    dsimp [α] at hx
    linarith


end StarShapedRisk.LawInvariant


set_option autoImplicit false
set_option maxHeartbeats 2000000
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

noncomputable def lr_open_uniform (U : Ω → ℝ) (ω : Ω) : Ioo (0:ℝ) 1 :=
  if h : U ω ∈ Ioo (0:ℝ) 1 then ⟨U ω,h⟩ else ⟨1/2,by norm_num⟩

lemma lr_open_uniform_measurable (U : Ω → ℝ) (hm : Measurable U) :
    Measurable (lr_open_uniform U) := by
  have hS : MeasurableSet {ω | U ω ∈ Ioo (0:ℝ) 1} := hm measurableSet_Ioo
  have he : (fun ω => (lr_open_uniform U ω).val) =
      {ω | U ω ∈ Ioo (0:ℝ) 1}.piecewise U (fun _ => 1/2) := by
    funext ω
    by_cases h : U ω ∈ Ioo (0:ℝ) 1
    · simp only [lr_open_uniform, dif_pos h, Set.piecewise, mem_setOf_eq, if_pos h]
    · simp only [lr_open_uniform, dif_neg h, Set.piecewise, mem_setOf_eq, if_neg h]
  have hf : Measurable (fun ω => (lr_open_uniform U ω).val) := by
    rw [he]
    exact hm.piecewise hS measurable_const
  exact hf.subtype_mk

lemma lr_atomless_open_uniform (hP : IsAtomless P) :
    ∃ U : Ω → Ioo (0:ℝ) 1, Measurable U ∧
      ∀ t ∈ Icc (0:ℝ) 1, P.real {ω | (U ω).val ≤ t} = t := by
  obtain ⟨U,hm,hbounds,hcdf,hstrict⟩ := lr_atomless_uniform P hP
  have h0 : ∀ᵐ ω ∂P, 0 < U ω := by
    rw [ae_iff]
    simp only [not_lt]
    exact (measureReal_eq_zero_iff).mp (hcdf 0 (by norm_num))
  have h1 : ∀ᵐ ω ∂P, U ω < 1 := by
    rw [ae_iff]
    have he : P.real {ω | ¬ U ω < 1} = 0 := by
      have hs : MeasurableSet {ω | U ω < 1} := hm measurableSet_Iio
      have hh := measureReal_add_measureReal_compl (μ := P) hs
      rw [probReal_univ,hstrict] at hh
      change 1 + P.real {ω | ¬ U ω < 1} = 1 at hh
      linarith
    exact (measureReal_eq_zero_iff).mp he
  have hae : ∀ᵐ ω ∂P, (lr_open_uniform U ω).val = U ω := by
    filter_upwards [h0,h1] with ω h0 h1
    simp [lr_open_uniform, show U ω ∈ Ioo (0:ℝ) 1 from ⟨h0,h1⟩]
  refine ⟨lr_open_uniform U, lr_open_uniform_measurable U hm, ?_⟩
  intro t ht
  calc
    P.real {ω | (lr_open_uniform U ω).val ≤ t} = P.real {ω | U ω ≤ t} := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [hae] with ω hω
      apply propext
      change ((lr_open_uniform U ω).val ≤ t) ↔ U ω ≤ t
      rw [hω]
    _ = t := hcdf t ht

noncomputable def lr_quantile_position (U : Ω → Ioo (0:ℝ) 1) (hm : Measurable U)
    (X : Positions Ω) : Positions Ω :=
  ⟨fun ω => VaR P (U ω).val X.val,
    (lr_var_measurable_level P X).comp hm, by
    obtain ⟨C,hC⟩ := X.property.2
    exact ⟨C,fun ω => abs_le.mpr (lr_var_bounded P X C hC (U ω).val (U ω).property)⟩⟩

lemma lr_quantile_position_law (U : Ω → Ioo (0:ℝ) 1) (hm : Measurable U)
    (hU : ∀ t ∈ Icc (0:ℝ) 1, P.real {ω | (U ω).val ≤ t} = t) (X : Positions Ω) :
    P.map (lr_quantile_position P U hm X).val = P.map X.val := by
  haveI : IsProbabilityMeasure (P.map (lr_quantile_position P U hm X).val) :=
    Measure.isProbabilityMeasure_map (lr_quantile_position P U hm X).property.1.aemeasurable
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  intro t
  rw [cdf_eq_real, map_measureReal_apply (lr_quantile_position P U hm X).property.1 measurableSet_Iic]
  change P.real {ω | VaR P (U ω).val X.val ≤ t} = cdf (P.map X.val) t
  have he : {ω | VaR P (U ω).val X.val ≤ t} = {ω | (U ω).val ≤ cdf (P.map X.val) t} := by
    ext ω
    exact lr_quantile_le P X (U ω).val (U ω).property t
  rw [he]
  exact hU _ ⟨cdf_nonneg _ _,cdf_le_one _ _⟩

theorem fsd_consistent (hP : IsAtomless P)
    (ρ : Positions Ω → ℝ) (hmono : IsMonotone ρ) (hlaw : IsLawInvariant P ρ)
    (X Y : Positions Ω) (hXY : FSD P X.val Y.val) : ρ X ≤ ρ Y := by
  obtain ⟨U,hm,hU⟩ := lr_atomless_open_uniform P hP
  have hq : ∀ ω, (lr_quantile_position P U hm X).val ω ≤
      (lr_quantile_position P U hm Y).val ω := by
    intro ω
    exact (eqA1_fsd_iff_VaR_le P X Y).mp hXY (U ω).val (U ω).property
  have hx := hlaw (lr_quantile_position P U hm X) X (lr_quantile_position_law P U hm hU X)
  have hy := hlaw (lr_quantile_position P U hm Y) Y (lr_quantile_position_law P U hm hU Y)
  rw [← hx, ← hy]
  exact hmono _ _ hq

end StarShapedRisk.LawInvariant

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace StarShapedRisk.LawInvariant

lemma lr_star_small {Ω : Type*} [MeasurableSpace Ω] (ρ : Positions Ω → ℝ)
    (hs : IsStarShaped ρ) (X : Positions Ω) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ρ (t • X) ≤ t * ρ X := by
  have hh := hs (t • X) t⁻¹ ((one_lt_inv₀ ht0).mpr ht1)
  rw [smul_smul,inv_mul_cancel₀ ht0.ne',one_smul] at hh
  have hm := mul_le_mul_of_nonneg_left hh ht0.le
  simpa [← mul_assoc,mul_inv_cancel₀ ht0.ne'] using hm


lemma lr_risk_const {Ω : Type*} [MeasurableSpace Ω] (ρ : Positions Ω → ℝ)
    (hρ : IsRiskMeasure ρ) (m : ℝ) : ρ (const m)=m := by
  have he : (0 : Positions Ω)-const (-m)=const m := by ext ω; simp [const]
  have hh := hρ.2.1 0 (-m)
  have hn : ρ 0=0 := hρ.2.2
  rw [he,hn] at hh
  simpa using hh

lemma lr_shifts_bounds {Ω : Type*} [MeasurableSpace Ω] (A : Set (Positions Ω))
    (hA : IsAcceptanceSet A) (X : Positions Ω) :
    {m : ℝ | X-const m ∈ A}.Nonempty ∧ BddBelow {m : ℝ | X-const m ∈ A} := by
  obtain ⟨C,hC⟩ := X.property.2
  obtain ⟨m,hm⟩ := hA.1.nonempty
  constructor
  · refine ⟨C-m,hA.2 (const m) hm (X-const (C-m)) ?_⟩
    intro ω
    change X.val ω-(C-m) ≤ m
    have := (abs_le.mp (hC ω)).2
    linarith
  · refine ⟨-C,?_⟩
    intro m hm
    have hac : const (-C-m) ∈ A := hA.2 _ hm _ (by
      intro ω
      change -C-m ≤ X.val ω-m
      have := (abs_le.mp (hC ω)).1
      linarith)
    have hh := hA.1.1 hac
    change -C-m ≤ 0 at hh
    linarith

theorem proposition2_star_shaped_tfae {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Positions Ω → ℝ) (hρ : IsRiskMeasure ρ) :
    List.TFAE
      [IsStarShaped ρ,
       StarConvex ℝ (0 : Positions Ω) (acceptanceSetOf ρ),
       ∃ A : Set (Positions Ω), IsAcceptanceSet A ∧ StarConvex ℝ (0 : Positions Ω) A ∧
         ρ = rhoOf A] := by
  tfae_have 1 → 2
  · intro hs Y hY a b ha hb hab
    simp only [smul_zero,zero_add]
    change ρ (b • Y) ≤ 0
    change ρ Y ≤ 0 at hY
    rcases eq_or_lt_of_le hb with hb|hb
    · rw [← hb,zero_smul]
      exact le_of_eq hρ.2.2
    rcases eq_or_lt_of_le (show b ≤ 1 by linarith) with hb1|hb1
    · simpa only [hb1,one_smul] using hY
    · exact (lr_star_small ρ hs Y b hb hb1).trans (mul_nonpos_of_nonneg_of_nonpos hb.le hY)
  tfae_have 2 → 3
  · intro hs
    refine ⟨acceptanceSetOf ρ,?_,hs,?_⟩
    · constructor
      · have he : {m : ℝ | const m ∈ acceptanceSetOf ρ}=Set.Iic 0 := by
          ext m
          simp only [acceptanceSetOf,Set.mem_setOf_eq,Set.mem_Iic,lr_risk_const ρ hρ]
        rw [he]
        exact isLUB_Iic
      · intro X hX Y hYX
        exact (hρ.1 X Y hYX).trans hX
    · funext X
      have he : {m : ℝ | X-const m ∈ acceptanceSetOf ρ}=Set.Ici (ρ X) := by
        ext m
        change ρ (X-const m) ≤ 0 ↔ ρ X ≤ m
        rw [hρ.2.1]
        exact sub_nonpos
      simp only [rhoOf,he,csInf_Ici]
  tfae_have 3 → 1
  · rintro ⟨A,hA,hs,rfl⟩ X t ht
    have ht0 : 0 < t := by linarith
    apply le_csInf (lr_shifts_bounds A hA (t • X)).1
    intro m hm
    have he : (1-t⁻¹) • (0 : Positions Ω) + t⁻¹ • (t • X-const m) = X-const (m/t) := by
      ext ω
      simp only [Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Submodule.coe_zero,Pi.zero_apply,
        Submodule.coe_sub,Pi.sub_apply,const]
      field_simp
      ring
    have hx : X-const (m/t) ∈ A := by
      rw [← he]
      exact hs hm (sub_nonneg.mpr ((inv_lt_one₀ ht0).mpr ht).le) (inv_pos.mpr ht0).le (by ring)
    have hi : rhoOf A X ≤ m/t := csInf_le (lr_shifts_bounds A hA X).2 hx
    simpa only [mul_comm] using (le_div_iff₀ ht0).mp hi
  tfae_finish


end StarShapedRisk.LawInvariant

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

noncomputable def lr_envelope (Z X : Positions Ω) : ℝ :=
  sSup (Set.range (fun α : Ioo (0 : ℝ) 1 => VaR P α.val X.val - VaR P α.val Z.val))

lemma lr_envelope_bounds (Z X : Positions Ω) :
    (Set.range (fun α : Ioo (0 : ℝ) 1 => VaR P α.val X.val - VaR P α.val Z.val)).Nonempty ∧
    BddAbove (Set.range (fun α : Ioo (0 : ℝ) 1 => VaR P α.val X.val - VaR P α.val Z.val)) := by
  obtain ⟨C, hC⟩ := X.property.2
  obtain ⟨D, hD⟩ := Z.property.2
  refine ⟨⟨_, ⟨⟨1/2, by constructor <;> norm_num⟩, rfl⟩⟩, C+D, ?_⟩
  rintro r ⟨α, rfl⟩
  have hx := lr_var_bounded P X C hC α.val α.property
  have hz := lr_var_bounded P Z D hD α.val α.property
  linarith

lemma lr_envelope_dominates (ρ : Positions Ω → ℝ) (hρ : IsRiskMeasure ρ)
    (hcons : ∀ X Y : Positions Ω, FSD P X.val Y.val → ρ X ≤ ρ Y)
    (Z X : Positions Ω) (hZ : ρ Z ≤ 0) : ρ X ≤ lr_envelope P Z X := by
  have hs : FSD P (X-const (lr_envelope P Z X)).val Z.val := by
    apply (eqA1_fsd_iff_VaR_le P _ _).mpr
    intro α hα
    rw [lr_var_cash P X α hα]
    have hh := le_csSup (lr_envelope_bounds P Z X).2
      (show VaR P α X.val - VaR P α Z.val ∈ Set.range
        (fun a : Ioo (0 : ℝ) 1 => VaR P a.val X.val - VaR P a.val Z.val) from ⟨⟨α,hα⟩,rfl⟩)
    change VaR P α X.val - VaR P α Z.val ≤ lr_envelope P Z X at hh
    linarith
  have hh := hcons _ Z hs
  rw [hρ.2.1] at hh
  linarith

lemma lr_envelope_attains (ρ : Positions Ω → ℝ) (hρ : IsRiskMeasure ρ) (X : Positions Ω) :
    lr_envelope P (X-const (ρ X)) X = ρ X := by
  apply le_antisymm
  · apply csSup_le (lr_envelope_bounds P _ X).1
    rintro r ⟨α, rfl⟩
    dsimp only
    rw [lr_var_cash P X α.val α.property]
    linarith
  · apply le_csSup (lr_envelope_bounds P (X-const (ρ X)) X).2
    refine ⟨⟨1/2, by constructor <;> norm_num⟩, ?_⟩
    dsimp only
    rw [lr_var_cash P X _ (by constructor <;> norm_num)]
    ring

lemma lr_envelope_minimum (ρ : Positions Ω → ℝ) (hρ : IsRiskMeasure ρ)
    (hcons : ∀ X Y : Positions Ω, FSD P X.val Y.val → ρ X ≤ ρ Y) (X : Positions Ω) :
    IsLeast ((fun Z => lr_envelope P Z X) '' acceptanceSetOf ρ) (ρ X) := by
  refine ⟨⟨X-const (ρ X), ?_, lr_envelope_attains P ρ hρ X⟩, ?_⟩
  · change ρ (X-const (ρ X)) ≤ 0
    rw [hρ.2.1]; exact le_of_eq (sub_self _)
  · rintro r ⟨Z, hZ, rfl⟩
    exact lr_envelope_dominates P ρ hρ hcons Z X hZ

lemma lr_accepted_quantiles_star (ρ : Positions Ω → ℝ) (hρ : IsRiskMeasure ρ)
    (hs : IsStarShaped ρ) :
    StarConvex ℝ 0 ((fun X : Positions Ω => fun α : Ioo (0 : ℝ) 1 => VaR P α.val X.val) '' acceptanceSetOf ρ) := by
  have ha : StarConvex ℝ 0 (acceptanceSetOf ρ) := by
    have ht := proposition2_star_shaped_tfae ρ hρ
    exact (ht.out 0 1 (by rfl) (by rfl)).mp hs
  rintro g ⟨X, hX, rfl⟩ a b ha0 hb0 hab
  rcases eq_or_lt_of_le hb0 with hb | hb
  · have hz : (0 : Positions Ω) ∈ acceptanceSetOf ρ := le_of_eq hρ.2.2
    refine ⟨0, hz, ?_⟩
    funext α
    have he : const (Ω := Ω) 0 = (0 : Positions Ω) := by ext ω; rfl
    dsimp only
    rw [← he, lr_var_const P 0 α.val α.property]
    simp [← hb]
  · refine ⟨b • X, ?_, ?_⟩
    · simpa only [smul_zero, zero_add] using ha hX ha0 hb0 hab
    · funext α
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero, zero_add]
      exact lr_var_scale P X α.val α.property b hb
end StarShapedRisk.LawInvariant

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma lr_ereal_sup {ι : Type*} [Nonempty ι] (f : ι → ℝ) (hb : BddAbove (range f)) :
    (⨆ i, (f i : EReal)) = ((sSup (range f) : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact_mod_cast le_csSup hb (mem_range_self i)
  · let y : EReal := ⨆ i, (f i : EReal)
    change ((sSup (range f) : ℝ) : EReal) ≤ y
    by_cases ht : y = ⊤
    · simp [ht]
    have hbot : y ≠ ⊥ := by
      obtain ⟨i⟩ := ‹Nonempty ι›
      have hh : (f i : EReal) ≤ y := le_iSup (fun j => (f j : EReal)) i
      exact ne_of_gt ((EReal.bot_lt_coe (f i)).trans_le hh)
    have he := EReal.coe_toReal ht hbot
    have hs : sSup (range f) ≤ y.toReal := csSup_le (range_nonempty f) (by
      rintro r ⟨i,rfl⟩
      have hh := le_iSup (fun j => (f j : EReal)) i
      change (f i : EReal) ≤ y at hh
      rw [← he] at hh
      exact_mod_cast hh)
    rw [← he]
    exact_mod_cast hs

lemma lr_accepted_quantile_inf (hP : IsAtomless P) (ρ : Positions Ω → ℝ)
    (hρ : IsRiskMeasure ρ) (hlaw : IsLawInvariant P ρ)
    (Z : Positions Ω) (hZ : ρ Z ≤ 0) :
    (⨅ α : Ioo (0:ℝ) 1, (VaR P α.val Z.val : EReal)) ≤ 0 := by
  let I : EReal := ⨅ α : Ioo (0:ℝ) 1, (VaR P α.val Z.val : EReal)
  change I ≤ 0
  by_contra h
  have hp : (0:EReal) < I := lt_of_not_ge h
  have hbot : I ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe 0).trans hp)
  have hi : I ≤ (VaR P (1/2) Z.val : EReal) :=
    iInf_le (fun α : Ioo (0:ℝ) 1 => (VaR P α.val Z.val : EReal)) ⟨1/2,by norm_num⟩
  have htop : I ≠ ⊤ := ne_of_lt (hi.trans_lt (EReal.coe_lt_top _))
  have he := EReal.coe_toReal htop hbot
  have hr : 0 < I.toReal := by rw [← he] at hp; exact_mod_cast hp
  have horder : FSD P (const I.toReal).val Z.val := by
    apply (eqA1_fsd_iff_VaR_le P _ Z).mpr
    intro α hα
    rw [lr_var_const P I.toReal α hα]
    have hh := iInf_le (fun a : Ioo (0:ℝ) 1 => (VaR P a.val Z.val : EReal)) ⟨α,hα⟩
    change I ≤ (VaR P α Z.val : EReal) at hh
    rw [← he] at hh
    exact_mod_cast hh
  have hh := fsd_consistent P hP ρ hρ.1 hlaw (const I.toReal) Z horder
  rw [lr_risk_const ρ hρ] at hh
  linarith

lemma lr_representation_forward (hP : IsAtomless P) (ρ : Positions Ω → ℝ)
    (hρ : IsRiskMeasure ρ) (hs : IsStarShaped ρ) (hlaw : IsLawInvariant P ρ) :
    ∃ G : Set (Ioo (0:ℝ) 1 → ℝ), StarConvex ℝ 0 G ∧
      (∀ g ∈ G, Monotone g ∧ (⨅ α : Ioo (0:ℝ) 1, (g α : EReal)) ≤ 0) ∧
      ∀ X : Positions Ω, (ρ X : EReal) =
        ⨅ g ∈ G, ⨆ α : Ioo (0:ℝ) 1, ((VaR P α.val X.val - g α : ℝ) : EReal) := by
  let G : Set (Ioo (0:ℝ) 1 → ℝ) :=
    (fun Z : Positions Ω => fun α : Ioo (0:ℝ) 1 => VaR P α.val Z.val) '' acceptanceSetOf ρ
  have hc : ∀ X Y : Positions Ω, FSD P X.val Y.val → ρ X ≤ ρ Y :=
    fun X Y hXY => fsd_consistent P hP ρ hρ.1 hlaw X Y hXY
  refine ⟨G,lr_accepted_quantiles_star P ρ hρ hs,?_,?_⟩
  · rintro g ⟨Z,hZ,rfl⟩
    exact ⟨lr_var_monotone_level P Z,lr_accepted_quantile_inf P hP ρ hρ hlaw Z hZ⟩
  · intro X
    haveI : Nonempty (Ioo (0:ℝ) 1) := ⟨⟨1/2,by norm_num⟩⟩
    have he : ∀ Z : Positions Ω,
        (⨆ α : Ioo (0:ℝ) 1, ((VaR P α.val X.val - VaR P α.val Z.val : ℝ) : EReal)) =
          (lr_envelope P Z X : EReal) := by
      intro Z
      exact lr_ereal_sup _ (lr_envelope_bounds P Z X).2
    apply le_antisymm
    · apply le_iInf
      intro g
      apply le_iInf
      rintro ⟨Z,hZ,rfl⟩
      rw [he Z]
      exact_mod_cast lr_envelope_dominates P ρ hρ hc Z X hZ
    · let Z := X-const (ρ X)
      have hZ : Z ∈ acceptanceSetOf ρ := by
        change ρ (X-const (ρ X)) ≤ 0
        rw [hρ.2.1]; simp
      have hg : (fun α : Ioo (0:ℝ) 1 => VaR P α.val Z.val) ∈ G := ⟨Z,hZ,rfl⟩
      have hfirst : (⨅ g ∈ G, ⨆ α : Ioo (0:ℝ) 1,
          ((VaR P α.val X.val-g α:ℝ):EReal)) ≤
          (⨆ α : Ioo (0:ℝ) 1, ((VaR P α.val X.val-VaR P α.val Z.val:ℝ):EReal)) :=
        iInf_le_of_le (fun α : Ioo (0:ℝ) 1 => VaR P α.val Z.val) (iInf_le_of_le hg le_rfl)
      apply le_trans hfirst
      rw [he Z,lr_envelope_attains P ρ hρ X]

end StarShapedRisk.LawInvariant

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

def LrUpperAt (X : Positions Ω) (g : Ioo (0:ℝ) 1 → ℝ) (r : ℝ) : Prop :=
  ∀ α, VaR P α.val X.val - g α ≤ r

noncomputable def lr_robust_value (G : Set (Ioo (0:ℝ) 1 → ℝ)) (X : Positions Ω) : EReal :=
  ⨅ g ∈ G, ⨆ α : Ioo (0:ℝ) 1, ((VaR P α.val X.val - g α : ℝ) : EReal)

lemma lr_rep_le (ρ : Positions Ω → ℝ) (G : Set (Ioo (0:ℝ) 1 → ℝ))
    (hrep : ∀ X, (ρ X : EReal) = lr_robust_value P G X)
    (X : Positions Ω) (g : Ioo (0:ℝ) 1 → ℝ) (hg : g ∈ G) (r : ℝ)
    (hu : LrUpperAt P X g r) : ρ X ≤ r := by
  have hh : (ρ X : EReal) ≤ (r:EReal) := by
    rw [hrep X]
    have hfirst : lr_robust_value P G X ≤
        (⨆ α : Ioo (0:ℝ) 1, ((VaR P α.val X.val-g α:ℝ):EReal)) :=
      iInf_le_of_le g (iInf_le_of_le hg le_rfl)
    apply le_trans hfirst
    apply iSup_le
    intro α
    exact_mod_cast hu α
  exact_mod_cast hh

lemma lr_rep_approx (ρ : Positions Ω → ℝ) (G : Set (Ioo (0:ℝ) 1 → ℝ))
    (hrep : ∀ X, (ρ X : EReal) = lr_robust_value P G X)
    (X : Positions Ω) (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ G, LrUpperAt P X g (ρ X+ε) := by
  have hh : lr_robust_value P G X < (ρ X+ε:EReal) := by
    rw [← hrep X]
    exact_mod_cast (show ρ X < ρ X+ε by linarith)
  obtain ⟨g,hg⟩ := iInf_lt_iff.mp hh
  obtain ⟨hG,hg⟩ := iInf_lt_iff.mp hg
  refine ⟨g,hG,?_⟩
  intro α
  have hα : ((VaR P α.val X.val-g α:ℝ):EReal) ≤ (ρ X+ε:EReal) :=
    (le_iSup (fun a : Ioo (0:ℝ) 1 => ((VaR P a.val X.val-g a:ℝ):EReal)) α).trans hg.le
  exact_mod_cast hα

lemma lr_var_zero (α : Ioo (0:ℝ) 1) : VaR P α.val (0 : Positions Ω).val = 0 := by
  have he : const (Ω := Ω) 0 = (0 : Positions Ω) := by ext ω; rfl
  rw [← he, lr_var_const P 0 α.val α.property]

lemma lr_contract_mem (G : Set (Ioo (0:ℝ) 1 → ℝ)) (hG : StarConvex ℝ 0 G)
    (g : Ioo (0:ℝ) 1 → ℝ) (hg : g ∈ G) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    b • g ∈ G := by
  simpa only [smul_zero,zero_add] using hG hg (sub_nonneg.mpr hb1) hb0 (show 1-b+b=1 by ring)

lemma lr_upper_zero_nonneg (g : Ioo (0:ℝ) 1 → ℝ)
    (hg : (⨅ α : Ioo (0:ℝ) 1, (g α:EReal)) ≤ 0)
    (r : ℝ) (hu : LrUpperAt P 0 g r) : 0 ≤ r := by
  have hh : (-r:EReal) ≤ (⨅ α : Ioo (0:ℝ) 1, (g α:EReal)) := by
    apply le_iInf
    intro α
    have h := hu α
    rw [lr_var_zero P α] at h
    exact_mod_cast (show -r ≤ g α by linarith)
  have h := hh.trans hg
  have hz : -r ≤ (0:ℝ) := by exact_mod_cast h
  linarith

lemma lr_rep_normalized (ρ : Positions Ω → ℝ) (G : Set (Ioo (0:ℝ) 1 → ℝ))
    (hG : StarConvex ℝ 0 G)
    (hzero : ∀ g ∈ G, (⨅ α : Ioo (0:ℝ) 1, (g α:EReal)) ≤ 0)
    (hrep : ∀ X, (ρ X : EReal) = lr_robust_value P G X) : IsNormalized ρ := by
  have hn : 0 ≤ ρ 0 := by
    by_contra h
    have hlt : ρ 0 < 0 := lt_of_not_ge h
    obtain ⟨g,hg,hu⟩ := lr_rep_approx P ρ G hrep 0 (-ρ 0/2) (by linarith)
    have hh := lr_upper_zero_nonneg P g (hzero g hg) (ρ 0+(-ρ 0/2)) hu
    linarith
  apply le_antisymm ?_ hn
  by_contra h
  have hp : 0 < ρ 0 := lt_of_not_ge h
  obtain ⟨g,hg,hu⟩ := lr_rep_approx P ρ G hrep 0 1 (by norm_num)
  let r : ℝ := ρ 0+1
  let b : ℝ := ρ 0/(2*r)
  have hr : 0 < r := by dsimp [r]; linarith
  have hb0 : 0 ≤ b := div_nonneg hp.le (by positivity)
  have hb1 : b ≤ 1 := (div_le_one (by positivity : 0 < 2*r)).mpr (by dsimp [r]; linarith)
  have hbg := lr_contract_mem G hG g hg b hb0 hb1
  have hub : LrUpperAt P 0 (b • g) (b*r) := by
    intro α
    have hh := hu α
    rw [lr_var_zero P α] at hh
    have hm := mul_le_mul_of_nonneg_left hh hb0
    rw [lr_var_zero P α]
    simp only [Pi.smul_apply,smul_eq_mul]
    dsimp only [r] at *
    nlinarith
  have hh := lr_rep_le P ρ G hrep 0 (b • g) hbg (b*r) hub
  have he : b*r = ρ 0/2 := by dsimp [b]; field_simp
  rw [he] at hh
  linarith

lemma lr_rep_monotone (ρ : Positions Ω → ℝ) (G : Set (Ioo (0:ℝ) 1 → ℝ))
    (hrep : ∀ X, (ρ X : EReal) = lr_robust_value P G X) : IsMonotone ρ := by
  intro X Y hYX
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨g,hg,hu⟩ := lr_rep_approx P ρ G hrep X ε hε
  apply lr_rep_le P ρ G hrep Y g hg (ρ X+ε)
  intro α
  have hq := lr_var_monotone_loss P Y X hYX α.val α.property
  have hh := hu α
  linarith

lemma lr_rep_cash (ρ : Positions Ω → ℝ) (G : Set (Ioo (0:ℝ) 1 → ℝ))
    (hrep : ∀ X, (ρ X : EReal) = lr_robust_value P G X) : IsTranslationInvariant ρ := by
  intro X m
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g,hg,hu⟩ := lr_rep_approx P ρ G hrep X ε hε
    apply lr_rep_le P ρ G hrep (X-const m) g hg (ρ X-m+ε)
    intro α
    rw [lr_var_cash P X α.val α.property m]
    have hh := hu α
    linarith
  · have h : ρ X ≤ ρ (X-const m)+m := by
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨g,hg,hu⟩ := lr_rep_approx P ρ G hrep (X-const m) ε hε
      apply lr_rep_le P ρ G hrep X g hg (ρ (X-const m)+m+ε)
      intro α
      have hh := hu α
      rw [lr_var_cash P X α.val α.property m] at hh
      linarith
    linarith

lemma lr_rep_law (ρ : Positions Ω → ℝ) (G : Set (Ioo (0:ℝ) 1 → ℝ))
    (hrep : ∀ X, (ρ X : EReal) = lr_robust_value P G X) : IsLawInvariant P ρ := by
  intro X Y hlaw
  have h : ∀ A B : Positions Ω, P.map A.val = P.map B.val → ρ A ≤ ρ B := by
    intro A B hAB
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g,hg,hu⟩ := lr_rep_approx P ρ G hrep B ε hε
    apply lr_rep_le P ρ G hrep A g hg (ρ B+ε)
    intro α
    rw [lr_var_law_invariant P A B hAB α.val α.property]
    exact hu α
  exact le_antisymm (h X Y hlaw) (h Y X hlaw.symm)

lemma lr_rep_star (ρ : Positions Ω → ℝ) (G : Set (Ioo (0:ℝ) 1 → ℝ))
    (hG : StarConvex ℝ 0 G)
    (hrep : ∀ X, (ρ X : EReal) = lr_robust_value P G X) : IsStarShaped ρ := by
  intro X t ht
  have ht0 : 0 < t := by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨g,hg,hu⟩ := lr_rep_approx P ρ G hrep (t • X) ε hε
  have hgt : (1/t) • g ∈ G := lr_contract_mem G hG g hg (1/t)
    (by positivity) ((div_le_one ht0).mpr ht.le)
  have hub : LrUpperAt P X ((1/t) • g) ((ρ (t • X)+ε)/t) := by
    intro α
    have hh := hu α
    rw [lr_var_scale P X α.val α.property t ht0] at hh
    simp only [Pi.smul_apply,smul_eq_mul]
    apply (le_div_iff₀ ht0).mpr
    have he : (VaR P α.val X.val-(1/t)*g α)*t = t*VaR P α.val X.val-g α := by
      field_simp
    rw [he]
    exact hh
  have hh := lr_rep_le P ρ G hrep X ((1/t) • g) hgt ((ρ (t • X)+ε)/t) hub
  have hmul := (le_div_iff₀ ht0).mp hh
  nlinarith

lemma lr_representation_reverse (ρ : Positions Ω → ℝ) (G : Set (Ioo (0:ℝ) 1 → ℝ))
    (hG : StarConvex ℝ 0 G)
    (hprops : ∀ g ∈ G, Monotone g ∧ (⨅ α : Ioo (0:ℝ) 1, (g α:EReal)) ≤ 0)
    (hrep : ∀ X, (ρ X : EReal) = lr_robust_value P G X) :
    IsRiskMeasure ρ ∧ IsStarShaped ρ ∧ IsLawInvariant P ρ := by
  exact ⟨⟨lr_rep_monotone P ρ G hrep,lr_rep_cash P ρ G hrep,
    lr_rep_normalized P ρ G hG (fun g hg => (hprops g hg).2) hrep⟩,
    lr_rep_star P ρ G hG hrep,lr_rep_law P ρ G hrep⟩

end StarShapedRisk.LawInvariant

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace StarShapedRisk.LawInvariant

open MeasureTheory

/-- Castagnoli et al. (2022), Theorem 5 (i)⇔(ii) (pp. 2646–2647). On an atomless probability
space, a function `ρ` on bounded measurable positions is a star-shaped, law-invariant risk
measure if and only if there is a star-shaped set `G` of increasing functions
`g : (0,1) → ℝ` with `g(0+) ≤ 0` such that
`ρ X = inf_{g ∈ G} sup_{α ∈ (0,1)} (VaR_α(X) - g α)` for every `X`
(computed in the extended reals). -/
theorem theorem5_star_shaped_law_invariant_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (ρ : Positions Ω → ℝ) :
    (IsRiskMeasure ρ ∧ IsStarShaped ρ ∧ IsLawInvariant P ρ) ↔
      ∃ G : Set (Set.Ioo (0 : ℝ) 1 → ℝ),
        StarConvex ℝ 0 G ∧
        (∀ g ∈ G, Monotone g ∧ ⨅ α : Set.Ioo (0 : ℝ) 1, (g α : EReal) ≤ 0) ∧
        ∀ X : Positions Ω,
          (ρ X : EReal) =
            ⨅ g ∈ G, ⨆ α : Set.Ioo (0 : ℝ) 1, ((VaR P α X.1 - g α : ℝ) : EReal) := by
  constructor
  · rintro ⟨hρ,hs,hlaw⟩
    exact lr_representation_forward P hP ρ hρ hs hlaw
  · rintro ⟨G,hG,hprops,hrep⟩
    exact lr_representation_reverse P ρ G hG hprops hrep

end StarShapedRisk.LawInvariant


open StarShapedRisk.LawInvariant

open MeasureTheory

/-- Castagnoli et al. (2022), Theorem 5 (i)⇔(ii) (pp. 2646–2647). On an atomless probability
space, a function `ρ` on bounded measurable positions is a star-shaped, law-invariant risk
measure if and only if there is a star-shaped set `G` of increasing functions
`g : (0,1) → ℝ` with `g(0+) ≤ 0` such that
`ρ X = inf_{g ∈ G} sup_{α ∈ (0,1)} (VaR_α(X) - g α)` for every `X`
(computed in the extended reals). -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (ρ : Positions Ω → ℝ) :
    (IsRiskMeasure ρ ∧ IsStarShaped ρ ∧ IsLawInvariant P ρ) ↔
      ∃ G : Set (Set.Ioo (0 : ℝ) 1 → ℝ),
        StarConvex ℝ 0 G ∧
        (∀ g ∈ G, Monotone g ∧ ⨅ α : Set.Ioo (0 : ℝ) 1, (g α : EReal) ≤ 0) ∧
        ∀ X : Positions Ω,
          (ρ X : EReal) =
            ⨅ g ∈ G, ⨆ α : Set.Ioo (0 : ℝ) 1, ((VaR P α X.1 - g α : ℝ) : EReal) := by
  exact theorem5_star_shaped_law_invariant_iff P hP ρ


#check solution
#print axioms solution
