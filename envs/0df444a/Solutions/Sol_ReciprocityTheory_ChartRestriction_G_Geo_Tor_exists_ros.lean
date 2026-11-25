-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ros
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:12.341808+00:00
-- url     : https://prove2.me/submissions/5126959d-0f14-4cf5-82b9-a499837f9656

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable [IsCommMonObj A] {L : LB A.left}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (h : RosatiAdj A L f g) : ∃ u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) := by

  have loc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : LB.Gen (LB.LinComb L (K := Fin 6)
      (fun i => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g i) rosatiε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ ((A ⊗ A).hom ⁻¹ᵁ U).toScheme) (b : Z ⟶ S) (z : Z) (J), Good L z J →
        r ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = b ≫ zero2 A → val t r z J = 1 := by
    intro s
    obtain ⟨U, hs, t, ht⟩ := h s
    have z2 : zero2 A ≫ (A ⊗ A).hom = 𝟙 S := Over.w (lift η[A] η[A])
    obtain ⟨n, n₁⟩ : ∃ n : ((A ⊗ A).hom ⁻¹ᵁ U).toScheme ⟶ ((A ⊗ A).hom ⁻¹ᵁ U).toScheme,
        n ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (A ⊗ A).hom ≫ zero2 A :=
      ⟨IsOpenImmersion.lift ((A ⊗ A).hom ⁻¹ᵁ U).ι (((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (A ⊗ A).hom ≫ zero2 A) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e := congrArg (fun q => q ((A ⊗ A).hom y.1)) z2
        exact (congrArg (· ∈ U) e).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    let T₀ : Over S := Over.mk (((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (A ⊗ A).hom)
    have n₂ : n ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = (lift (1 : T₀ ⟶ A) (1 : T₀ ⟶ A)).left := by
      have : lift (1 : T₀ ⟶ A) (1 : T₀ ⟶ A) = toUnit T₀ ≫ lift η[A] η[A] := by rw [comp_lift]; rfl
      rw [n₁, this, ← Category.assoc]; rfl
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := fun i => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g i) (ε' := rosatiε)
      (fun V _ k => by
        have p := prod_ros f g (1 : T₀ ⟶ A) (1 : T₀ ⟶ A) k
        rw [← n₂, MonObj.one_comp, MonObj.one_comp, _root_.mul_one] at p
        refine Eq.trans (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
          (c := ∏ i, k (((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g i) ^ rosatiε i) rfl
          (DVR.prod_neg _ _ ((Finset.prod_congr rfl fun i _ => by rw [Category.assoc]; rfl).trans p))) ?_
        simp)
      (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
    refine ⟨U, hs, t', ht', fun Z r b z J hJ hr => ?_⟩
    have : r ≫ n = r := by
      rw [← cancel_mono ((A ⊗ A).hom ⁻¹ᵁ U).ι, Category.assoc, n₁, ← Category.assoc, hr, Category.assoc,
        ← Category.assoc (zero2 A), z2]
      exact congrArg (b ≫ ·) (Category.id_comp _)
    rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]
  choose U hU t ht hn using loc

  have agree : ∀ (s s' : S) (Z : Scheme.{0}) (r : Z ⟶ ((A ⊗ A).hom ⁻¹ᵁ U s).toScheme)
      (r' : Z ⟶ ((A ⊗ A).hom ⁻¹ᵁ U s').toScheme) (z : Z) (J), Good L z J →
      r ≫ ((A ⊗ A).hom ⁻¹ᵁ U s).ι = r' ≫ ((A ⊗ A).hom ⁻¹ᵁ U s').ι → val (t s) r z J = val (t s') r' z J := by
    intro s s' Z r r' z J hJ hr
    let V : Over S := Over.mk (U s ⊓ U s').ι
    let pr : A ⊗ A ⊗ V ⟶ A ⊗ A := lift (fst _ _) (snd _ _ ≫ fst _ _)
    have mk : ∀ W : S.Opens, U s ⊓ U s' ≤ W → ∃ m : (A ⊗ A ⊗ V).left ⟶ ((A ⊗ A).hom ⁻¹ᵁ W).toScheme,
        m ≫ ((A ⊗ A).hom ⁻¹ᵁ W).ι = pr.left := fun W hW =>
      ⟨IsOpenImmersion.lift ((A ⊗ A).hom ⁻¹ᵁ W).ι pr.left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e := congrArg (fun q => q y) ((Over.w pr).trans (Over.w (snd A (A ⊗ V) ≫ snd A V)).symm)
        exact (congrArg (· ∈ W) e).mpr (hW ((snd A (A ⊗ V) ≫ snd A V).left y).2)), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨m, hm⟩ := mk (U s) inf_le_left
    obtain ⟨m', hm'⟩ := mk (U s') inf_le_right
    let e : V ⟶ A ⊗ A ⊗ V := lift 1 (lift 1 (𝟙 V))
    have he : e ≫ pr = toUnit V ≫ lift η[A] η[A] := by rw [comp_lift, comp_lift]; simp [e, Hom.one_def]
    let TZ : Over S := Over.mk ((r ≫ ((A ⊗ A).hom ⁻¹ᵁ U s).ι) ≫ (A ⊗ A).hom)
    let xy : TZ ⟶ A ⊗ A := Over.homMk (r ≫ ((A ⊗ A).hom ⁻¹ᵁ U s).ι) rfl
    let v : TZ ⟶ V := Over.homMk (IsOpenImmersion.lift (U s ⊓ U s').ι TZ.hom (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact ⟨(r y).2, (congrArg (fun q => (A ⊗ A).hom (q y) ∈ U s') hr).mpr (r' y).2⟩)) (IsOpenImmersion.lift_fac _ _ _)
    let ρ : TZ ⟶ A ⊗ A ⊗ V := lift (xy ≫ fst _ _) (lift (xy ≫ snd _ _) v)
    have hρ : ρ ≫ pr = xy := by ext <;> simp [ρ, pr]
    have hρ' : ρ.left ≫ pr.left = r ≫ ((A ⊗ A).hom ⁻¹ᵁ U s).ι := congrArg (fun q => q.left) hρ
    have r₁ : ρ.left ≫ m = r := by rw [← cancel_mono ((A ⊗ A).hom ⁻¹ᵁ U s).ι, Category.assoc, hm, hρ']
    have r₂ : ρ.left ≫ m' = r' := by rw [← cancel_mono ((A ⊗ A).hom ⁻¹ᵁ U s').ι, Category.assoc, hm', hρ', hr]
    have key := gen_unique' hL (φ := fun i => m ≫ ((A ⊗ A).hom ⁻¹ᵁ U s).ι ≫ rosatiφ A f g i) (ε := rosatiε)
      (φ' := fun i => m' ≫ ((A ⊗ A).hom ⁻¹ᵁ U s').ι ≫ rosatiφ A f g i) (ε' := rosatiε)
      (fun W _ k => Finset.prod_congr rfl fun i _ => by
        show k (m' ≫ _ ≫ _) ^ _ = k (m ≫ _ ≫ _) ^ _
        rw [← Category.assoc, ← Category.assoc m, hm, hm'])
      ((snd A (A ⊗ V)).left ≫ (snd A V).left) e.left (by
        rw [← Over.comp_left, ← Over.comp_left]
        exact congrArg (fun q => q.left) (show e ≫ snd A (A ⊗ V) ≫ snd A V = 𝟙 V by simp [e]))
      (surj_comp (surj_snd hG hA _) (surj_snd hG hA _)) (DVR.pullGen_isGen _ _ _ _ (ht s) m)
      (DVR.pullGen_isGen _ _ _ _ (ht s') m') (fun y I hI => by
        have he' : e.left ≫ pr.left = V.hom ≫ zero2 A := congrArg (fun q => q.left) he
        rw [val_pull hI, val_pull hI, hn s _ _ V.hom y I hI (by rw [Category.assoc, hm, he']),
          hn s' _ _ V.hom y I hI (by rw [Category.assoc, hm', he'])]) Z ρ.left z J hJ
    rwa [val_pull hJ, val_pull hJ, r₁, r₂] at key
  obtain ⟨u, hu, hv⟩ := glue_gen hL (rosatiφ A f g) rosatiε (fun s => (A ⊗ A).hom ⁻¹ᵁ U s)
    (fun y => ⟨(A ⊗ A).hom y, hU _⟩) t ht agree
  refine ⟨u, hu, fun j j' c₁ _ _ => unit_ext fun y hy => ?_⟩

  have z2 : zero2 A ≫ (A ⊗ A).hom = 𝟙 S := Over.w (lift η[A] η[A])
  let z : (U y).toScheme := ⟨y, hU y⟩
  obtain ⟨r, hr⟩ : ∃ r : (U y).toScheme ⟶ ((A ⊗ A).hom ⁻¹ᵁ U y).toScheme,
      r ≫ ((A ⊗ A).hom ⁻¹ᵁ U y).ι = (U y).ι ≫ zero2 A :=
    ⟨IsOpenImmersion.lift _ ((U y).ι ≫ zero2 A) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (· ∈ U y) (congrArg (fun m => m q.1) z2)).mpr q.2), IsOpenImmersion.lift_fac _ _ _⟩
  have all : ∀ a b, zero2 A ≫ rosatiφ A f g a = zero2 A ≫ rosatiφ A f g b := by
    have one : ∀ a, zero2 A ≫ rosatiφ A f g a = η[A].left := fun a => by
      have e : ∀ q : A ⊗ A ⟶ A, lift η[A] η[A] ≫ q = η[A] → zero2 A ≫ q.left = η[A].left := fun q hq =>
        congrArg (fun m => m.left) hq
      have o : lift η[A] η[A] ≫ μ[A] = η[A] := by simpa [Hom.one_def, Hom.mul_def] using
        (_root_.mul_one (1 : 𝟙_ (Over S) ⟶ A))
      fin_cases a <;> refine e _ ?_ <;> simp [padd, comp_lift_assoc, o]
    exact fun a b => (one a).trans (one b).symm
  obtain ⟨J, hJ, eJ⟩ := exists_good L hL z (fun k => (U y).ι ≫ zero2 A ≫ rosatiφ A f g k) j
    (fun a b _ => c₁ a b (all a b)) (fun k => Set.mem_iInter.1 hy.1 k)
  have v := (val_pull hJ u (zero2 A) (U y).ι).trans (by rw [← hr, hv y _ r z J hJ, hn y _ r (U y).ι z J hJ hr] :
    val u ((U y).ι ≫ zero2 A) z J = 1)
  rw [val_of _ (U y).ι z J j eJ] at v
  have hz : (U y).ι z ∈ LB.wchart L (fun k => zero2 A ≫ rosatiφ A f g k) j ⊓ LB.wchart L PEmpty.elim j' := hy
  exact gm_inj (U y).ι z hz hz (((gm_res _ z _ hz _).trans v).trans ((gm_res _ z _ hz _).trans (map_one _)).symm)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
