-- Prove2me | solution 1 for StarShapedRisk.LawInvariant.fsd_consistent
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T06:51:47.01016+00:00
-- url     : https://prove2.me/submissions/45d6772e-4016-4c0a-a966-606dfa7788d6

import Definitions.Def_StarShapedRisk_LawInvariant_Model
import Definitions.Def_StarShapedRisk_LawInvariant_VaR

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

open StarShapedRisk.LawInvariant

open MeasureTheory

/-- Castagnoli et al. (2022), proof of Theorem 5, the display after (A.1) (p. 2652): on an
atomless probability space, a monotone and law-invariant `ρ` is consistent with first-order
stochastic dominance: `X ≿FSD Y ⇒ ρ X ≤ ρ Y`. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (ρ : Positions Ω → ℝ) (hmono : IsMonotone ρ) (hlaw : IsLawInvariant P ρ)
    (X Y : Positions Ω) (hXY : FSD P X.1 Y.1) :
    ρ X ≤ ρ Y := by
  exact fsd_consistent P hP ρ hmono hlaw X Y hXY


#check solution
#print axioms solution
