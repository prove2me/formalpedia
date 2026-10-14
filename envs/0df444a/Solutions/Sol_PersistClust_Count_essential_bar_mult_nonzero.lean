-- Prove2me | solution 1 for PersistClust.Count.essential_bar_mult_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T18:20:49.293971+00:00
-- url     : https://prove2.me/submissions/7a155fef-3384-4541-868d-4effcffc498c

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

theorem structMap_comp {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u)
    (C : comps stage J u) :
    structMap hLaw hst (structMap hLaw htu C) = structMap hLaw (le_trans hst htu) C := by
  have hjoin : J s (compRep stage J t (structMap hLaw htu C)) (compRep stage J u C) := by
    have h1 : (fun x => {y | J t x y}) (compRep stage J t (structMap hLaw htu C)) =
        {y | J t (compRep stage J u C) y} :=
      (compRep_spec stage J t (structMap hLaw htu C)).2.trans (structMap_val hLaw htu C)
    have h2 : J t (compRep stage J t (structMap hLaw htu C)) (compRep stage J u C) := by
      have h3 : compRep stage J u C ∈ {y | J t (compRep stage J u C) y} :=
        hLaw.refl (hLaw.antitone htu (compRep_spec stage J u C).1)
      rw [← h1] at h3
      exact h3
    exact hLaw.compat hst h2
  have hval : (structMap hLaw hst (structMap hLaw htu C)).val =
      (structMap hLaw (le_trans hst htu) C).val := by
    ext y
    exact ⟨fun h => hLaw.trans (hLaw.symm hjoin) h, fun h => hLaw.trans hjoin h⟩
  exact Subtype.ext hval

theorem t3_rank_meets {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : t ≤ s) :
    rankFn stage J s t =
      {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage s)}.encard := by
  have hval : ((fun x => {y | J t x y}) '' stage s) =
      Subtype.val '' {C : comps stage J t |
        C.val ∈ ((fun x => {y | J t x y}) '' stage s)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hmem : {y | J t x y} ∈ ((fun x => {y | J t x y}) '' stage t) :=
        ⟨x, hLaw.antitone hst hx, rfl⟩
      exact ⟨⟨{y | J t x y}, hmem⟩, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨C, hCS, hzC⟩
      subst hzC
      exact hCS
  unfold rankFn
  calc ((fun x => {y | J t x y}) '' stage s).encard
      = (Subtype.val '' {C : comps stage J t |
          C.val ∈ ((fun x => {y | J t x y}) '' stage s)}).encard := congrArg Set.encard hval
    _ = {C : comps stage J t |
          C.val ∈ ((fun x => {y | J t x y}) '' stage s)}.encard :=
        Subtype.val_injective.encard_image _

theorem t3_structMap_id {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) :
    structMap hLaw le_rfl C = C :=
  Subtype.ext (compRep_spec stage J t C).2

theorem t3_desc_point {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {t u : ℝ} (hst : t ≤ u)
    {C : comps stage J t} {C' : comps stage J u} (hC' : structMap hLaw hst C' = C)
    {z : ι} (hz : z ∈ C'.val) :
    ((fun x => {y | J t x y}) z) = C.val ∧ z ∈ stage t := by
  have hspec := compRep_spec stage J u C'
  have hzr : J u (compRep stage J u C') z :=
    (Set.ext_iff.mp hspec.2 z).mpr hz
  have hzrt : J t (compRep stage J u C') z := hLaw.compat hst hzr
  have hfmr : ((fun x => {y | J t x y}) (compRep stage J u C')) = C.val := by
    have hv : (structMap hLaw hst C').val = C.val := congrArg Subtype.val hC'
    rw [structMap_val] at hv
    exact hv
  have hclasses : ((fun x => {y | J t x y}) z) =
      ((fun x => {y | J t x y}) (compRep stage J u C')) := by
    ext y
    constructor
    · intro hy
      exact hLaw.trans hzrt hy
    · intro hy
      exact hLaw.trans (hLaw.symm hzrt) hy
  exact ⟨hclasses.trans hfmr, (hLaw.mem hzrt).2⟩

theorem rungB_bSup_descend_ge {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {t t' : ℝ} (hle : t' ≤ t) (E : comps stage J t) :
    birthSup hLaw t E ≤ birthSup hLaw t' (structMap hLaw hle E) := by
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  have hBddT : BddAbove (AncSet hLaw t' (structMap hLaw hle E)) := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle'
    push_neg at hle'
    exact hstage.ne_empty (hs₀ u hle'.le)
  have hne : (AncSet hLaw t E).Nonempty := ⟨t, le_rfl, E, t3_structMap_id hLaw t E⟩
  refine csSup_le hne ?_
  intro u hu
  obtain ⟨hw', E', hE'⟩ := hu
  exact (rfl : birthSup hLaw t' (structMap hLaw hle E)
      = sSup (AncSet hLaw t' (structMap hLaw hle E))).symm ▸
    (le_csSup hBddT ⟨le_trans hle hw', E', by rw [← hE', structMap_comp hLaw hle hw' E']⟩)

/-- Essential-bar multiplicity bookkeeping: if the value-ray through a cell E
at level T is constantly e on EVERY level w <= T (the cell and every
descent of it carry birth-sup e), then the essential bar (e, bottom) has
positive multiplicity: for every eta > 0 and t <= e - eta the level-t
descent of E (or, above T, the descent of an ancestor of E) has birth-sup
in (e - eta, e], meets stage (e - eta) but not stage (e + eta), so every
rank difference in the bottom-branch infimum of mult is at least 1. -/
theorem solution {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {T e : ℝ} (E : comps stage J T) (he : birthSup hLaw T E = e)
    (hfull : ∀ (w : ℝ) (hw : w ≤ T), birthSup hLaw w (structMap hLaw hw E) = e) :
    mult (rankFn stage J) ((e : EReal), (⊥ : EReal)) ≠ 0 := by
  classical
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  -- (0) every ancestor-level set is bounded above by s₀ (cells are nonempty ⊆ their stage)
  have hAncBdd : ∀ {t : ℝ} (C : comps stage J t), BddAbove (AncSet hLaw t C) := by
    intro t C
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C', -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C'.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  -- (1) the census witness: for every (η, t) a level-t cell with birth-sup in (e−η, e]
  have hwit : ∀ (η : ℝ), 0 < η → ∀ (t : ℝ), t ≤ e - η →
      ∃ (F : comps stage J t), e - η < birthSup hLaw t F ∧ birthSup hLaw t F ≤ e := by
    intro η hη t ht
    by_cases hTt : t ≤ T
    · refine ⟨structMap hLaw hTt E, ?_, ?_⟩
      · rw [hfull t hTt]; linarith
      · rw [hfull t hTt]
    · have hTt2 : T ≤ t := (lt_of_not_ge hTt).le
      have hBne : (AncSet hLaw T E).Nonempty := ⟨T, le_refl T, E, t3_structMap_id hLaw T E⟩
      have hsup : sSup (AncSet hLaw T E) = e :=
        (rfl : sSup (AncSet hLaw T E) = birthSup hLaw T E).symm.trans he
      have hlt : e - η < sSup (AncSet hLaw T E) := by rw [hsup]; linarith
      obtain ⟨u, huB, huη⟩ := (lt_csSup_iff (hAncBdd E) hBne).mp hlt
      obtain ⟨hu, C', hC'⟩ := huB
      have htu : t ≤ u := (lt_of_le_of_lt ht huη).le
      have hdesc : structMap hLaw hTt2 (structMap hLaw htu C') = E := by
        rw [structMap_comp hLaw hTt2 htu C']
        exact hC'
      refine ⟨structMap hLaw htu C', ?_, ?_⟩
      · have hmem : u ∈ AncSet hLaw t (structMap hLaw htu C') := ⟨htu, C', rfl⟩
        have hle : u ≤ birthSup hLaw t (structMap hLaw htu C') :=
          (rfl : birthSup hLaw t (structMap hLaw htu C') =
              sSup (AncSet hLaw t (structMap hLaw htu C'))).symm ▸
            le_csSup (hAncBdd _) hmem
        linarith
      · have hball : ∀ w ∈ AncSet hLaw t (structMap hLaw htu C'), w ≤ e := by
          intro w hw
          obtain ⟨hw, C'', hC''⟩ := hw
          have hC''E : structMap hLaw (le_trans hTt2 hw) C'' = E := by
            rw [← structMap_comp hLaw hTt2 hw C'', hC'']
            exact hdesc
          have hr : birthSup hLaw w C'' ≤ e := by
            have hrun := rungB_bSup_descend_ge hLaw hTame (le_trans hTt2 hw) C''
            rw [hC''E, he] at hrun
            exact hrun
          have hwle : w ≤ birthSup hLaw w C'' :=
            (rfl : birthSup hLaw w C'' = sSup (AncSet hLaw w C'')).symm ▸
              le_csSup (hAncBdd _) ⟨le_refl w, C'', t3_structMap_id hLaw w C''⟩
          linarith
        have hBne2 : (AncSet hLaw t (structMap hLaw htu C')).Nonempty :=
          ⟨t, le_refl t, _, t3_structMap_id hLaw t _⟩
        exact csSup_le hBne2 hball
  -- (2) the rank difference is ≥ 1 for every (η, t)
  have hge : ∀ (η : ℝ), 0 < η → ∀ (t : ℝ), t ≤ e - η →
      1 ≤ rankFn stage J (e - η) t - rankFn stage J (e + η) t := by
    intro η hη t ht
    obtain ⟨F, hFhi, hFlo⟩ := hwit η hη t ht
    haveI hfinT : Finite (comps stage J t) := (hTame.1 t).to_subtype
    -- F meets stage (e − η): an ancestor level above e − η contributes a point
    have hBneF : (AncSet hLaw t F).Nonempty := ⟨t, le_refl t, F, t3_structMap_id hLaw t F⟩
    have hsupF : sSup (AncSet hLaw t F) = birthSup hLaw t F := rfl
    have hltF : e - η < sSup (AncSet hLaw t F) := by rw [hsupF]; exact hFhi
    obtain ⟨u, huB, huη⟩ := (lt_csSup_iff (hAncBdd F) hBneF).mp hltF
    obtain ⟨hu, C', hC'⟩ := huB
    have hspec := compRep_spec stage J u C'
    have hz : compRep stage J u C' ∈ C'.val := by
      rw [← hspec.2]
      exact hLaw.refl hspec.1
    obtain ⟨hcls, -⟩ := t3_desc_point hLaw hu hC' hz
    have hFS₁ : F ∈ {C : comps stage J t |
        C.val ∈ ((fun x => {y | J t x y}) '' stage (e - η))} :=
      ⟨compRep stage J u C', hLaw.antitone (show (e - η) ≤ u by linarith) hspec.1, hcls⟩
    -- F does not meet stage (e + η): a meeting point would put e + η into F's AncSet
    have hF2 : F ∉ {C : comps stage J t |
        C.val ∈ ((fun x => {y | J t x y}) '' stage (e + η))} := by
      intro hF
      obtain ⟨x, hx, hxcls⟩ := hF
      have hprop : {y | J (e + η) x y} ∈
          ((fun x => {y | J (e + η) x y}) '' stage (e + η)) := ⟨x, hx, rfl⟩
      have hdesc : structMap hLaw (show t ≤ e + η by linarith)
          ⟨{y | J (e + η) x y}, hprop⟩ = F := by
        have hspec := compRep_spec stage J (e + η) ⟨{y | J (e + η) x y}, hprop⟩
        have hJsx : J (e + η) (compRep stage J (e + η) ⟨{y | J (e + η) x y}, hprop⟩) x :=
          (Set.ext_iff.mp hspec.2 x).mpr (hLaw.refl hx)
        have hJtx : J t (compRep stage J (e + η) ⟨{y | J (e + η) x y}, hprop⟩) x :=
          hLaw.compat (show t ≤ e + η by linarith) hJsx
        refine Subtype.ext ?_
        rw [structMap_val, ← hxcls]
        ext y
        exact ⟨fun hy => hLaw.trans (hLaw.symm hJtx) hy, fun hy => hLaw.trans hJtx hy⟩
      have hmem : (e + η) ∈ AncSet hLaw t F :=
        ⟨show t ≤ e + η by linarith, _, hdesc⟩
      have hle : (e + η) ≤ birthSup hLaw t F :=
        (rfl : birthSup hLaw t F = sSup (AncSet hLaw t F)).symm ▸
          le_csSup (hAncBdd F) hmem
      linarith
    -- the strict count: the (e + η)-meeters are a proper subset of the (e − η)-meeters
    have hsub : {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e + η))}
        ⊆ {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e - η))} := by
      intro C hC
      obtain ⟨x, hx, hxcls⟩ := hC
      exact ⟨x, hLaw.antitone (show (e - η) ≤ (e + η) by linarith) hx, hxcls⟩
    have hfinS : {C : comps stage J t |
        C.val ∈ ((fun x => {y | J t x y}) '' stage (e + η))}.Finite :=
      Set.Finite.subset Set.finite_univ (Set.subset_univ _)
    have hssub : {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e + η))}
        ⊂ {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e - η))} :=
      ⟨hsub, fun heq => hF2 (heq hFS₁)⟩
    have hlt := hfinS.encard_lt_encard hssub
    have hne : {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e - η))}.encard -
        {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e + η))}.encard ≠ 0 :=
      fun hzero => not_le.mpr hlt (tsub_eq_zero_iff_le.mp hzero)
    rw [t3_rank_meets hLaw (show t ≤ e - η by linarith),
        t3_rank_meets hLaw (show t ≤ e + η by linarith)]
    exact ENat.one_le_iff_ne_zero.mpr hne
  -- (3) the ⊥-branch of `mult` is ≥ 1
  have hopen : mult (rankFn stage J) ((e : EReal), (⊥ : EReal)) =
      ⨅ (η : ℝ) (_ : 0 < η), ⨅ (t : ℝ) (_ : t ≤ e - η),
        (rankFn stage J (e - η) t - rankFn stage J (e + η) t) := by
    simp only [mult]
    rw [if_pos (⟨EReal.coe_ne_bot e, EReal.coe_ne_top e⟩ :
        ((e : EReal) ≠ (⊥ : EReal)) ∧ ((e : EReal) ≠ (⊤ : EReal))),
      if_pos (trivial : True)]
    simp only [EReal.toReal_coe]
  have h1 : 1 ≤ mult (rankFn stage J) ((e : EReal), (⊥ : EReal)) := by
    rw [hopen]
    exact le_iInf₂ fun η hη => le_iInf₂ fun t ht => hge η hη t ht
  exact ENat.one_le_iff_ne_zero.mp h1
