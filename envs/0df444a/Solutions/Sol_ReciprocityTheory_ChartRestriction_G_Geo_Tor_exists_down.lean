-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:33.055148+00:00
-- url     : https://prove2.me/submissions/41e7f69c-6955-435a-adcb-d4d9f6fd833a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pw_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_of_gm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
section Transport
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
private theorem mem_wchart_lemma {A B : Scheme.{0}} {Idx : Type} [Fintype Idx] (M : LB A) (ψ : Idx → (B ⟶ A))
    (j : Idx → M.ι) (b : B) : b ∈ LB.wchart M ψ j ↔ ∀ k, ψ k b ∈ M.U (j k) := by
  show b ∈ ⋂ k, (ψ k).base ⁻¹' (M.U (j k) : Set A) ↔ _
  exact Set.mem_iInter
private theorem gm_res_pullU_lemma_2 {A B C : Scheme.{0}} (f : B ⟶ A) (U : A.Opens) (V : B.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (r : C ⟶ B) (c : C) (hc : r c ∈ V) (s : Γ(A, U)ˣ) :
    gm r c V (res h (pullU f U s)) = gm (r ≫ f) c U s := by
  have hc' : (r ≫ f) c ∈ U := by simpa using h hc
  unfold gm
  rw [dif_pos hc, dif_pos hc']
  have hc2 : c ∈ r ⁻¹ᵁ V := hc
  have hc3 : c ∈ r ⁻¹ᵁ f ⁻¹ᵁ U := hc'
  have key : f.app U ≫ B.presheaf.map (homOfLE h).op ≫ r.app V ≫ C.presheaf.germ (r ⁻¹ᵁ V) c hc2 =
      f.app U ≫ r.app (f ⁻¹ᵁ U) ≫ C.presheaf.germ (r ⁻¹ᵁ f ⁻¹ᵁ U) c hc3 := by
    rw [Scheme.Hom.naturality_assoc, TopCat.Presheaf.germ_res]
  ext
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (s : Γ(A, U))) key
private theorem gm_res_lemma_4 {B C : Scheme.{0}} {U V : B.Opens} (h : V ≤ U) (r : C ⟶ B) (c : C)
    (hc : r c ∈ V) (s : Γ(B, U)ˣ) : gm r c V (res h s) = gm r c U s := by
  have hc' : r c ∈ U := h hc
  unfold gm
  rw [dif_pos hc, dif_pos hc']
  have hc2 : c ∈ r ⁻¹ᵁ V := hc
  have hc3 : c ∈ r ⁻¹ᵁ U := hc'
  have key : B.presheaf.map (homOfLE h).op ≫ r.app V ≫ C.presheaf.germ (r ⁻¹ᵁ V) c hc2 =
      r.app U ≫ C.presheaf.germ (r ⁻¹ᵁ U) c hc3 := by
    rw [Scheme.Hom.naturality_assoc, TopCat.Presheaf.germ_res]
  ext
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (s : Γ(B, U))) key
private theorem gm_id_lemma_6 {A : Scheme.{0}} (V : A.Opens) (y : A) (hy : y ∈ V) (s : Γ(A, V)ˣ) :
    ((gm (𝟙 A) y V s : A.presheaf.stalk y)) = A.presheaf.germ V y hy (s : Γ(A, V)) := by
  have hy1 : (𝟙 A) y ∈ V := by simpa using hy
  simp only [gm, dif_pos hy1]
  first
  | rfl
  | simp [pullU]
private theorem glue_units_lemma_5 {A : Scheme.{0}} {I : Type} (V : A.Opens) (U : I → A.Opens)
    (hU : ∀ i, U i ≤ V) (hcov : ∀ y ∈ V, ∃ i, y ∈ U i) (σ : ∀ i, Γ(A, U i)ˣ)
    (hσ : ∀ i j (y : A), y ∈ U i → y ∈ U j → gm (𝟙 A) y (U i) (σ i) = gm (𝟙 A) y (U j) (σ j)) :
    ∃ s : Γ(A, V)ˣ, ∀ i, res (hU i) s = σ i := by
  have hcover : V ≤ iSup U := fun y hy => Opens.mem_iSup.mpr (hcov y hy)
  have compat : ∀ τ : ∀ i, Γ(A, U i)ˣ,
      (∀ i j (y : A), y ∈ U i → y ∈ U j → gm (𝟙 A) y (U i) (τ i) = gm (𝟙 A) y (U j) (τ j)) →
      TopCat.Presheaf.IsCompatible A.sheaf.1 U (fun i => ((τ i : Γ(A, U i)))) := by
    intro τ hτ i j
    refine TopCat.Presheaf.section_ext A.sheaf _ _ _ fun y hy => ?_
    have h := congrArg Units.val (hτ i j y hy.1 hy.2)
    rw [gm_id_lemma_6 _ _ hy.1, gm_id_lemma_6 _ _ hy.2] at h
    have e1 : A.presheaf.germ (U i ⊓ U j) y hy (A.presheaf.map (Opens.infLELeft (U i) (U j)).op
        (τ i : Γ(A, U i))) = A.presheaf.germ (U i) y hy.1 (τ i : Γ(A, U i)) := by
      rw [TopCat.Presheaf.germ_res_apply]
    have e2 : A.presheaf.germ (U i ⊓ U j) y hy (A.presheaf.map (Opens.infLERight (U i) (U j)).op
        (τ j : Γ(A, U j))) = A.presheaf.germ (U j) y hy.2 (τ j : Γ(A, U j)) := by
      rw [TopCat.Presheaf.germ_res_apply]
    exact e1.trans (h.trans e2.symm)
  obtain ⟨s0, hs0, -⟩ := TopCat.Sheaf.existsUnique_gluing' A.sheaf U V (fun i => homOfLE (hU i)) hcover _
    (compat σ hσ)
  obtain ⟨s1, hs1, -⟩ := TopCat.Sheaf.existsUnique_gluing' A.sheaf U V (fun i => homOfLE (hU i)) hcover _
    (compat (fun i => (σ i)⁻¹) fun i j y hi hj => by
      show gm (𝟙 A) y (U i) (σ i)⁻¹ = gm (𝟙 A) y (U j) (σ j)⁻¹
      rw [map_inv, map_inv, hσ i j y hi hj])
  have germ_eq : ∀ (s : Γ(A, V)) (τ : ∀ i, Γ(A, U i)),
      (∀ i, A.presheaf.map (homOfLE (hU i)).op s = τ i) →
      ∀ (y : A) (hy : y ∈ V) (i : I) (hi : y ∈ U i),
        A.presheaf.germ V y hy s = A.presheaf.germ (U i) y hi (τ i) := by
    intro s τ hs y hy i hi
    rw [← hs i, TopCat.Presheaf.germ_res_apply]
  have h01 : (s0 : Γ(A, V)) * (s1 : Γ(A, V)) = 1 := by
    refine TopCat.Presheaf.section_ext A.sheaf V _ _ fun y hy => ?_
    obtain ⟨i, hi⟩ := hcov y hy
    have e0 := germ_eq s0 _ hs0 y hy i hi
    have e1 := germ_eq s1 _ hs1 y hy i hi
    have e : A.presheaf.germ V y hy ((s0 : Γ(A, V)) * (s1 : Γ(A, V))) = A.presheaf.germ V y hy 1 := by
      calc A.presheaf.germ V y hy ((s0 : Γ(A, V)) * (s1 : Γ(A, V)))
          = A.presheaf.germ V y hy s0 * A.presheaf.germ V y hy s1 := map_mul _ _ _
        _ = A.presheaf.germ (U i) y hi ((σ i : Γ(A, U i))) *
              A.presheaf.germ (U i) y hi (((σ i)⁻¹ : Γ(A, U i)ˣ) : Γ(A, U i)) := by rw [e0, e1]
        _ = A.presheaf.germ (U i) y hi ((σ i * (σ i)⁻¹ : Γ(A, U i)ˣ) : Γ(A, U i)) := by
              rw [Units.val_mul, map_mul]
        _ = A.presheaf.germ V y hy 1 := by
              rw [_root_.mul_inv_cancel, Units.val_one, map_one, map_one]
    exact e
  exact ⟨⟨s0, s1, h01, (_root_.mul_comm (s1 : Γ(A, V)) (s0 : Γ(A, V))).trans h01⟩, fun i => Units.ext (hs0 i)⟩
private theorem gm_of_isGen_lemma_7 {A B : Scheme.{0}} {Idx : Type} [Fintype Idx] {M : LB A}
    {ψ : Idx → (B ⟶ A)} {ex : Idx → ℤ} (t : LB.Gen (LB.LinComb M ψ ex)) (ht : t.IsGen) (y : B)
    (i j : Idx → M.ι) (hi : y ∈ LB.wchart M ψ i) (hj : y ∈ LB.wchart M ψ j) :
    gm (𝟙 B) y (LB.wchart M ψ i) (t.s i) = trF ψ ex (𝟙 B) y i j * gm (𝟙 B) y (LB.wchart M ψ j) (t.s j) := by
  have hy : y ∈ LB.wchart M ψ i ⊓ LB.wchart M ψ j := ⟨hi, hj⟩
  have hk : ∀ k, LB.wchart M ψ i ⊓ LB.wchart M ψ j ≤ ψ k ⁻¹ᵁ (M.U (i k) ⊓ M.U (j k)) :=
    fun k => le_inf (inf_le_left.trans (LB.wchart_le M ψ i k)) (inf_le_right.trans (LB.wchart_le M ψ j k))
  have eg : gm (𝟙 B) y (LB.wchart M ψ i ⊓ LB.wchart M ψ j)
      (∏ k, res (hk k) (pullU (ψ k) (M.U (i k) ⊓ M.U (j k)) (M.g (i k) (j k))) ^ ex k) =
        trF ψ ex (𝟙 B) y i j := by
    simp only [trF, map_prod, map_zpow]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact congrArg (· ^ ex k) (gm_res_pullU_lemma_2 (ψ k) _ _ (hk k) (𝟙 B) y hy _)
  have e1 : gm (𝟙 B) y (LB.wchart M ψ i ⊓ LB.wchart M ψ j) (res inf_le_left (t.s i)) =
      gm (𝟙 B) y (LB.wchart M ψ i) (t.s i) := gm_res_lemma_4 inf_le_left (𝟙 B) y hy (t.s i)
  have e2 : gm (𝟙 B) y (LB.wchart M ψ i ⊓ LB.wchart M ψ j) (res inf_le_right (t.s j)) =
      gm (𝟙 B) y (LB.wchart M ψ j) (t.s j) := gm_res_lemma_4 inf_le_right (𝟙 B) y hy (t.s j)
  have h := congrArg (gm (𝟙 B) y _) (ht i j)
  rw [map_mul] at h
  exact e1.symm.trans (h.trans (congrArg₂ (· * ·) eg e2))
end Transport
section Pull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
end Pull
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen := by
  classical
  have hcovp : ∀ y : Y, ∃ p : K → L.ι, y ∈ LB.wchart L (fun k => φ' k ≫ F) p := by
    intro y
    have hk : ∀ k, ∃ i, (φ' k ≫ F) y ∈ L.U i := fun k =>
      Opens.mem_iSup.mp (by rw [hL.cover]; first | trivial | exact Set.mem_univ _ | simp)
    choose p hp using hk
    exact ⟨p, (mem_wchart_lemma _ _ _ _).mpr hp⟩
  choose u hu using fun p q => exists_pw w φ' ε p q
  have hle1 : ∀ q p, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      LB.wchart L (fun k => φ' k ≫ F) p := fun _ _ => inf_le_left
  have hle2 : ∀ q p, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      LB.wchart L' φ' q := fun _ _ => inf_le_right
  have key : ∀ {y : Y} (T P A : (Y.presheaf.stalk y)ˣ), (T * P)⁻¹ * (T * A) = P⁻¹ * A :=
    fun T P A => by rw [mul_inv_rev, _root_.mul_assoc, inv_mul_cancel_left]
  have key2 : ∀ {y : Y} (T P G : (Y.presheaf.stalk y)ˣ), (1 * T⁻¹ * P)⁻¹ * G = T * (P⁻¹ * G) :=
    fun T P G => by rw [_root_.one_mul, mul_inv_rev, inv_inv, _root_.mul_assoc, _root_.mul_left_comm]
  have hcompat : ∀ q p p' (y : Y), y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p' ⊓ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ ((u p q)⁻¹ * res (hle1 q p) (t.s p)) =
        gm (𝟙 Y) y _ ((u p' q)⁻¹ * res (hle1 q p') (t.s p')) := by
    intro q p p' y h1 h2
    have h1' : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := by simpa using h1
    have h2' : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p' ⊓ LB.wchart L' φ' q := by simpa using h2
    rw [map_mul, map_mul, map_inv, map_inv, hu p q Y (𝟙 Y) y h1', hu p' q Y (𝟙 Y) y h2',
      gm_res_lemma_4 (hle1 q p) (𝟙 Y) y h1' (t.s p), gm_res_lemma_4 (hle1 q p') (𝟙 Y) y h2' (t.s p'),
      pw_trans hw φ' ε (𝟙 Y) y h1'.1 h2'.1 h1'.2 h1'.2, trF_self hL' φ' ε (𝟙 Y) y h1'.2, inv_one,
      _root_.mul_one, gm_of_isGen_lemma_7 t ht y p p' h1.1 h2.1]
    exact key _ _ _
  have hglue : ∀ q, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ p,
      res (hle2 q p) s = (u p q)⁻¹ * res (hle1 q p) (t.s p) := fun q =>
    glue_units_lemma_5 _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (hle2 q)
      (fun y hy => ⟨(hcovp y).choose, (hcovp y).choose_spec, hy⟩)
      (fun p => (u p q)⁻¹ * res (hle1 q p) (t.s p)) (hcompat q)
  choose as has using hglue
  refine ⟨⟨as⟩, ?_⟩
  apply isGen_of_gm
  intro y q q' hq hq'
  obtain ⟨p, hp⟩ := hcovp y
  have hp1 : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p := by simpa using hp
  have hq1 : (𝟙 Y) y ∈ LB.wchart L' φ' q := by simpa using hq
  have hq1' : (𝟙 Y) y ∈ LB.wchart L' φ' q' := by simpa using hq'
  have hv : ∀ q₀ (hq₀ : (𝟙 Y) y ∈ LB.wchart L' φ' q₀), gm (𝟙 Y) y (LB.wchart L' φ' q₀) (as q₀) =
      (pw w φ' ε (𝟙 Y) y p q₀)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q₀ hq₀
    have hpq : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q₀ := ⟨hp1, hq₀⟩
    rw [← gm_res_lemma_4 (hle2 q₀ p) (𝟙 Y) y hpq (as q₀), has q₀ p, map_mul, map_inv, hu p q₀ Y (𝟙 Y) y hpq,
      gm_res_lemma_4 (hle1 q₀ p) (𝟙 Y) y hpq (t.s p)]
  show gm (𝟙 Y) y _ (as q) = _ * gm (𝟙 Y) y _ (as q')
  rw [hv q hq1, hv q' hq1', pw_trans hw φ' ε (𝟙 Y) y hp1 hp1 hq1 hq1', trF_self hL _ ε (𝟙 Y) y hp1]
  exact key2 _ _ _
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
