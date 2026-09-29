-- Prove2me | solution 1 for Submodule.exists_invertible_quotient_and_forall_localized_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5ea41fbf-7822-52db-a6b7-cd5821fa6fa7

import Mathlib
import Theorems.Thm_Module_Invertible_of_localization_maximal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_exists_invertible_quotient_and_forall_localized_eq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Pointwise

noncomputable section

namespace P2mKcGrassGlue

section Loc

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
variable {W : Type} [AddCommGroup W] [Module R W]
variable (y : PrimeSpectrum R) [Module (Localization.AtPrime y.asIdeal) W]
  [IsScalarTower R (Localization.AtPrime y.asIdeal) W]
  (g : V →ₗ[R] W) [IsLocalizedModule y.asIdeal.primeCompl g]

abbrev loc (N : Submodule R V) : Submodule (Localization.AtPrime y.asIdeal) W :=
  N.localized' (Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl g

theorem loc_mono {N P : Submodule R V} (h : N ≤ P) : loc y g N ≤ loc y g P := by
  rintro _ ⟨m, hm, s, rfl⟩
  exact ⟨m, h hm, s, rfl⟩

theorem mem_loc_of_mem {N : Submodule R V} {v : V} (hv : v ∈ N) : g v ∈ loc y g N :=
  ⟨v, hv, 1, IsLocalizedModule.mk'_one _ g v⟩

theorem loc_le_of_smul_le {N P : Submodule R V} (a : R) (ha : a ∉ y.asIdeal)
    (h : ∀ v ∈ N, a • v ∈ P) : loc y g N ≤ loc y g P := by
  refine Submodule.localized'_le_localized'_of_smul_le (Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl g
    (⟨a, ha⟩ : y.asIdeal.primeCompl) ?_
  intro m hm
  rw [Submonoid.smul_def, Submodule.mem_smul_pointwise_iff_exists] at hm
  obtain ⟨v, hv, rfl⟩ := hm
  exact h v hv

theorem loc_span_singleton_smul (N : Submodule R V) (a : R) (ha : a ∉ y.asIdeal) :
    loc y g ((Ideal.span {a} : Ideal R) • N) = loc y g N := by
  apply le_antisymm
  · exact loc_mono y g (Submodule.smul_le.mpr fun r _ n hn => N.smul_mem r hn)
  · refine loc_le_of_smul_le y g a ha fun v hv => ?_
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hv

end Loc

section Glue

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
variable (Vₚ : PrimeSpectrum R → Type) [∀ x, AddCommGroup (Vₚ x)] [∀ x, Module R (Vₚ x)]
  [∀ x, Module (Localization.AtPrime x.asIdeal) (Vₚ x)]
  [∀ x, IsScalarTower R (Localization.AtPrime x.asIdeal) (Vₚ x)]
  (f : ∀ x, V →ₗ[R] Vₚ x) [∀ x, IsLocalizedModule x.asIdeal.primeCompl (f x)]
  (Λ : ∀ x, Submodule (Localization.AtPrime x.asIdeal) (Vₚ x))

theorem exists_pow_smul_mem (c : R) (N N' : Submodule R V)
    (hNN' : ∀ z : PrimeSpectrum R, c ∉ z.asIdeal → loc z (f z) N = loc z (f z) N')
    (v : V) (hv : v ∈ N) : ∃ k : ℕ, c ^ k • v ∈ N' := by

  let J : Ideal R := N'.colon ({v} : Set V)
  have hJ : ∀ a : R, a ∈ J ↔ a • v ∈ N' := fun a => Submodule.mem_colon_singleton
  suffices hc : c ∈ J.radical by
    obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hc
    exact ⟨k, (hJ _).mp hk⟩
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro z ⟨hJz, hz⟩
  by_contra hcz
  let ζ : PrimeSpectrum R := ⟨z, hz⟩
  have hmem : f ζ v ∈ loc ζ (f ζ) N' := by
    rw [← hNN' ζ hcz]
    exact mem_loc_of_mem ζ (f ζ) hv
  obtain ⟨m, hm, s, hs⟩ := hmem
  rw [← IsLocalizedModule.mk'_one ζ.asIdeal.primeCompl (f ζ) v, IsLocalizedModule.mk'_eq_mk'_iff] at hs
  obtain ⟨u, hu⟩ := hs

  have hmem' : ((u : R) * (s : R)) • v ∈ N' := by
    have : (u : R) • (s : R) • v = (u : R) • m := by
      simpa [Submonoid.smul_def] using hu
    rw [mul_smul, this]
    exact N'.smul_mem _ hm
  have hnot : (u : R) * (s : R) ∉ z := by
    intro h
    rcases hz.mem_or_mem h with h1 | h2
    · exact u.2 h1
    · exact s.2 h2
  exact hnot (hJz ((hJ _).mpr hmem'))

theorem exists_pow_smul_le (c : R) (N N' : Submodule R V) (hN : N.FG)
    (hNN' : ∀ z : PrimeSpectrum R, c ∉ z.asIdeal → loc z (f z) N = loc z (f z) N') :
    ∃ K : ℕ, ∀ v ∈ N, c ^ K • v ∈ N' := by
  classical
  obtain ⟨G, hG⟩ := hN
  have hgen : ∀ w : V, ∃ k : ℕ, w ∈ G → c ^ k • w ∈ N' := by
    intro w
    by_cases hw : w ∈ G
    · obtain ⟨k, hk⟩ := exists_pow_smul_mem Vₚ f c N N' hNN' w (hG ▸ Submodule.subset_span hw)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => (hw h).elim⟩
  choose k hk using hgen
  refine ⟨G.sup k, ?_⟩
  have hgen' : ∀ w ∈ G, c ^ G.sup k • w ∈ N' := by
    intro w hw
    have hle : k w ≤ G.sup k := Finset.le_sup hw
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, add_comm, pow_add, mul_smul]
    exact N'.smul_mem _ (hk w hw)
  intro v hv
  rw [← hG] at hv
  induction hv using Submodule.span_induction with
  | mem w hw => exact hgen' w hw
  | zero => rw [smul_zero]; exact N'.zero_mem
  | add u w _ _ hu hw => rw [smul_add]; exact N'.add_mem hu hw
  | smul a w _ hw => rw [smul_comm]; exact N'.smul_mem a hw

variable (hloc : ∀ x : PrimeSpectrum R, ∃ r : R, r ∉ x.asIdeal ∧ ∃ N : Submodule R V, N.FG ∧
      ∀ y : PrimeSpectrum R, r ∉ y.asIdeal →
        Submodule.localized' (Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl (f y) N = Λ y)

include hloc in

theorem exists_fg_forall_loc_eq :
    ∃ N : Submodule R V, N.FG ∧ ∀ y : PrimeSpectrum R, loc y (f y) N = Λ y := by
  classical
  choose r hr N₀ hfg hN₀ using hloc

  have htop : (⨆ x : PrimeSpectrum R, (Ideal.span {r x} : Ideal R)) = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    have hx : r ⟨𝔪, h𝔪.isPrime⟩ ∈ 𝔪 :=
      hle (Submodule.mem_iSup_of_mem _ (Ideal.mem_span_singleton_self _))
    exact hr ⟨𝔪, h𝔪.isPrime⟩ hx
  have hone : (1 : R) ∈ ⨆ x : PrimeSpectrum R, (Ideal.span {r x} : Ideal R) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.exists_finset_of_mem_iSup _ hone

  have hcover : ∀ y : PrimeSpectrum R, ∃ x ∈ s, r x ∉ y.asIdeal := by
    intro y
    by_contra hall
    push Not at hall
    have hle : (⨆ x ∈ s, (Ideal.span {r x} : Ideal R)) ≤ y.asIdeal :=
      iSup₂_le fun x hx => (Ideal.span_singleton_le_iff_mem _).mpr (hall x hx)
    exact y.2.ne_top ((Ideal.eq_top_iff_one _).mpr (hle hs))

  have hpair : ∀ x x' : PrimeSpectrum R, ∃ K : ℕ, ∀ v ∈ N₀ x, (r x * r x') ^ K • v ∈ N₀ x' := by
    intro x x'
    refine exists_pow_smul_le Vₚ f (r x * r x') (N₀ x) (N₀ x') (hfg x) fun z hz => ?_
    have h1 : r x ∉ z.asIdeal := fun h => hz (z.asIdeal.mul_mem_right _ h)
    have h2 : r x' ∉ z.asIdeal := fun h => hz (z.asIdeal.mul_mem_left _ h)
    change Submodule.localized' _ _ (f z) (N₀ x) = Submodule.localized' _ _ (f z) (N₀ x')
    rw [hN₀ x z h1, hN₀ x' z h2]
  choose K hK using hpair
  let Km : ℕ := (s ×ˢ s).sup fun p => K p.1 p.2
  have hKm : ∀ x ∈ s, ∀ x' ∈ s, ∀ v ∈ N₀ x, (r x * r x') ^ Km • v ∈ N₀ x' := by
    intro x hx x' hx' v hv
    have hle : K x x' ≤ Km := Finset.le_sup (f := fun p : PrimeSpectrum R × PrimeSpectrum R => K p.1 p.2)
      (Finset.mk_mem_product hx hx')
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, add_comm, pow_add, mul_smul]
    exact (N₀ x').smul_mem _ (hK x x' v hv)

  let N : Submodule R V := ⨆ x ∈ s, (Ideal.span {r x ^ Km} : Ideal R) • N₀ x
  refine ⟨N, ?_, fun y => ?_⟩
  · exact Submodule.fg_biSup s _ fun x _ => Submodule.FG.smul (Submodule.fg_span_singleton _) (hfg x)
  obtain ⟨x₀, hx₀s, hx₀y⟩ := hcover y
  have hpow : r x₀ ^ Km ∉ y.asIdeal := fun h => hx₀y (y.2.mem_of_pow_mem _ h)
  apply le_antisymm
  ·
    have hsm : ∀ v ∈ N, r x₀ ^ Km • v ∈ N₀ x₀ := by
      intro v hv
      have hN_le : N ≤ (N₀ x₀).comap (LinearMap.lsmul R V (r x₀ ^ Km)) := by
        refine iSup₂_le fun x hx => Submodule.smul_le.mpr fun a ha w hw => ?_
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [Submodule.mem_comap, LinearMap.lsmul_apply]
        simp only [smul_smul]
        have hring : r x₀ ^ Km * (b * r x ^ Km) = b * (r x * r x₀) ^ Km := by ring
        rw [hring, mul_smul]
        exact (N₀ x₀).smul_mem b (hKm x hx x₀ hx₀s w hw)
      exact hN_le hv
    calc loc y (f y) N ≤ loc y (f y) (N₀ x₀) := loc_le_of_smul_le y (f y) _ hpow hsm
      _ = Λ y := hN₀ x₀ y hx₀y
  · calc Λ y = loc y (f y) (N₀ x₀) := (hN₀ x₀ y hx₀y).symm
      _ = loc y (f y) ((Ideal.span {r x₀ ^ Km} : Ideal R) • N₀ x₀) :=
          (loc_span_singleton_smul y (f y) (N₀ x₀) _ hpow).symm
      _ ≤ loc y (f y) N := loc_mono y (f y) (le_iSup₂_of_le x₀ hx₀s le_rfl)

end Glue

section Invertible

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
variable (Vₚ : PrimeSpectrum R → Type) [∀ x, AddCommGroup (Vₚ x)] [∀ x, Module R (Vₚ x)]
  [∀ x, Module (Localization.AtPrime x.asIdeal) (Vₚ x)]
  [∀ x, IsScalarTower R (Localization.AtPrime x.asIdeal) (Vₚ x)]
  (f : ∀ x, V →ₗ[R] Vₚ x) [∀ x, IsLocalizedModule x.asIdeal.primeCompl (f x)]
  (Λ : ∀ x, Submodule (Localization.AtPrime x.asIdeal) (Vₚ x))

theorem invertible_localizedModule_quotient (N : Submodule R V) (y : PrimeSpectrum R)
    (hy : loc y (f y) N = Λ y)
    (hinv : Module.Invertible (Localization.AtPrime y.asIdeal) (Vₚ y ⧸ Λ y)) :
    Module.Invertible (Localization.AtPrime y.asIdeal) (LocalizedModule y.asIdeal.primeCompl (V ⧸ N)) := by
  haveI := hinv

  haveI h1 : Module.Invertible (Localization.AtPrime y.asIdeal) (Vₚ y ⧸ loc y (f y) N) :=
    Module.Invertible.congr (Submodule.quotEquivOfEq (Λ y) (loc y (f y) N) hy.symm)

  let q : V ⧸ N →ₗ[R] Vₚ y ⧸ loc y (f y) N :=
    N.toLocalizedQuotient' (Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl (f y)
  haveI : IsLocalizedModule y.asIdeal.primeCompl q :=
    IsLocalizedModule.toLocalizedQuotient' (Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl (f y) N
  let e : LocalizedModule y.asIdeal.primeCompl (V ⧸ N) ≃ₗ[R] Vₚ y ⧸ loc y (f y) N :=
    IsLocalizedModule.iso y.asIdeal.primeCompl q
  let e' : LocalizedModule y.asIdeal.primeCompl (V ⧸ N) ≃ₗ[Localization.AtPrime y.asIdeal] Vₚ y ⧸ loc y (f y) N :=
    e.extendScalarsOfIsLocalization y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)
  exact Module.Invertible.congr e'.symm

end Invertible

section Main

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] [Module.FinitePresentation R V]

theorem glue
    (Vₚ : PrimeSpectrum R → Type) [∀ x, AddCommGroup (Vₚ x)] [∀ x, Module R (Vₚ x)]
    [∀ x, Module (Localization.AtPrime x.asIdeal) (Vₚ x)]
    [∀ x, IsScalarTower R (Localization.AtPrime x.asIdeal) (Vₚ x)]
    (f : ∀ x, V →ₗ[R] Vₚ x) [∀ x, IsLocalizedModule x.asIdeal.primeCompl (f x)]
    (Λ : ∀ x, Submodule (Localization.AtPrime x.asIdeal) (Vₚ x))
    (hinv : ∀ x, Module.Invertible (Localization.AtPrime x.asIdeal) (Vₚ x ⧸ Λ x))
    (hloc : ∀ x : PrimeSpectrum R, ∃ r : R, r ∉ x.asIdeal ∧ ∃ N : Submodule R V, N.FG ∧
      ∀ y : PrimeSpectrum R, r ∉ y.asIdeal →
        Submodule.localized' (Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl (f y) N = Λ y) :
    ∃ N : Submodule R V, Module.Invertible R (V ⧸ N) ∧
      ∀ x : PrimeSpectrum R, Submodule.localized' (Localization.AtPrime x.asIdeal) x.asIdeal.primeCompl (f x) N = Λ x := by
  obtain ⟨N, hNfg, hN⟩ := exists_fg_forall_loc_eq Vₚ f Λ hloc
  refine ⟨N, ?_, hN⟩

  haveI : Module.FinitePresentation R (V ⧸ N) :=
    Module.finitePresentation_of_surjective N.mkQ (Submodule.mkQ_surjective N) (by rw [Submodule.ker_mkQ]; exact hNfg)

  refine Module.Invertible.of_localization_maximal fun P hP => ?_
  exact invertible_localizedModule_quotient Vₚ f Λ N ⟨P, hP.isPrime⟩ (hN ⟨P, hP.isPrime⟩) (hinv ⟨P, hP.isPrime⟩)

end Main

end P2mKcGrassGlue

end

open P2mKcGrassGlue in
theorem solution
    {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] [Module.FinitePresentation R V]
    (Vₚ : PrimeSpectrum R → Type) [∀ x, AddCommGroup (Vₚ x)] [∀ x, Module R (Vₚ x)]
    [∀ x, Module (Localization.AtPrime x.asIdeal) (Vₚ x)]
    [∀ x, IsScalarTower R (Localization.AtPrime x.asIdeal) (Vₚ x)]
    (f : ∀ x, V →ₗ[R] Vₚ x) [∀ x, IsLocalizedModule x.asIdeal.primeCompl (f x)]
    (Λ : ∀ x, Submodule (Localization.AtPrime x.asIdeal) (Vₚ x))
    (hinv : ∀ x, Module.Invertible (Localization.AtPrime x.asIdeal) (Vₚ x ⧸ Λ x))
    (hloc : ∀ x : PrimeSpectrum R, ∃ r : R, r ∉ x.asIdeal ∧ ∃ N : Submodule R V, N.FG ∧
      ∀ y : PrimeSpectrum R, r ∉ y.asIdeal →
        Submodule.localized' (Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl (f y) N = Λ y) :
    ∃ N : Submodule R V, Module.Invertible R (V ⧸ N) ∧
      ∀ x : PrimeSpectrum R, Submodule.localized' (Localization.AtPrime x.asIdeal) x.asIdeal.primeCompl (f x) N = Λ x :=
  glue Vₚ f Λ hinv hloc

end S_Submodule_exists_invertible_quotient_and_forall_localized_eq
end P2MW
export P2MW.S_Submodule_exists_invertible_quotient_and_forall_localized_eq (solution)
