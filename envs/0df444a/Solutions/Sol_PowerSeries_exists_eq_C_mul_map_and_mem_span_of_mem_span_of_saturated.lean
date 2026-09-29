-- Prove2me | solution 1 for PowerSeries.exists_eq_C_mul_map_and_mem_span_of_mem_span_of_saturated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/55ebb6ea-b2f5-5f80-ac11-3c49f9ae18ef

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_exists_eq_C_mul_map_and_mem_span_of_mem_span_of_saturated

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace PowerSeries
p2m_export "PowerSeries" "coeff_mk mk coeff_smul coe_one coeff_map smul_eq_C_mul ext map_eq_zero map C coeff coe_smul"
namespace SaturationLemmaSpan
p2m_open "PowerSeries"

p2m_open "PowerSeries P2MW.S_PowerSeries_exists_eq_C_mul_map_and_mem_span_of_mem_span_of_saturated.PowerSeries"

theorem linearIndependent_comp_ringHom {𝔽 k σ : Type*} [Field 𝔽] [Field k] (φ : 𝔽 →+* k) :
    ∀ (r : ℕ) (v : Fin r → σ → 𝔽), LinearIndependent 𝔽 v →
      LinearIndependent k (fun i => (φ ∘ v i : σ → k)) := by
  intro r
  induction r with
  | zero => intro v _; exact linearIndependent_empty_type
  | succ r ih =>
    intro v hv
    set w : σ → 𝔽 := v (Fin.last r) with hw
    have hw0 : w ≠ 0 := hv.ne_zero (Fin.last r)
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, w m₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw0 (funext hall)
    set α : Fin r → 𝔽 := fun i => v (Fin.castSucc i) m₀ / w m₀ with hα
    set v' : Fin r → σ → 𝔽 := fun i => v (Fin.castSucc i) - α i • w with hv'
    have hv'm₀ : ∀ i, v' i m₀ = 0 := fun i => by
      simp only [hv', hα, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_cancel₀ _ hm₀, sub_self]
    have hv'li : LinearIndependent 𝔽 v' := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      set g' : Fin (r + 1) → 𝔽 := Fin.snoc g (-(∑ i, g i * α i)) with hg'
      have hrel : ∑ i, g' i • v i = 0 := by
        rw [Fin.sum_univ_castSucc]
        simp only [hg', Fin.snoc_castSucc, Fin.snoc_last]
        have : ∑ i : Fin r, g i • v (Fin.castSucc i) =
            ∑ i : Fin r, g i • v' i + (∑ i, g i * α i) • w := by
          rw [Finset.sum_smul, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hv']
          rw [smul_sub, mul_smul, sub_add_cancel]
        rw [this, hg, zero_add, ← hw, neg_smul, add_neg_cancel]
      have hall := (Fintype.linearIndependent_iff.mp hv) g' hrel
      intro i
      have := hall (Fin.castSucc i)
      simpa [hg'] using this
    have ih' := ih v' hv'li
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hdec : ∀ i : Fin r, (φ ∘ v (Fin.castSucc i) : σ → k) =
        (φ ∘ v' i : σ → k) + φ (α i) • (φ ∘ w : σ → k) := by
      intro i
      funext m
      simp [hv', map_mul]
    set μ : k := c (Fin.last r) + ∑ i : Fin r, c (Fin.castSucc i) * φ (α i) with hμ
    have hsplit : ∑ i : Fin r, c (Fin.castSucc i) • (φ ∘ v' i : σ → k) + μ • (φ ∘ w : σ → k) = 0 := by
      have h1 : ∑ i, c i • (fun i => (φ ∘ v i : σ → k)) i =
          ∑ i : Fin r, c (Fin.castSucc i) • (φ ∘ v (Fin.castSucc i) : σ → k) +
            c (Fin.last r) • (φ ∘ w : σ → k) := by
        rw [Fin.sum_univ_castSucc]
      rw [h1] at hc
      have h2 : ∑ i : Fin r, c (Fin.castSucc i) • (φ ∘ v (Fin.castSucc i) : σ → k) =
          ∑ i : Fin r, c (Fin.castSucc i) • (φ ∘ v' i : σ → k) +
            (∑ i : Fin r, c (Fin.castSucc i) * φ (α i)) • (φ ∘ w : σ → k) := by
        rw [Finset.sum_smul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hdec i, smul_add, mul_smul]
      rw [h2, add_assoc, ← add_smul, add_comm (∑ i : Fin r, c (Fin.castSucc i) * φ (α i))] at hc
      exact hc
    have hμ0 : μ = 0 := by
      have := congrArg (fun f : σ → k => f m₀) hsplit
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Function.comp_apply, hv'm₀,
        map_zero, mul_zero, Finset.sum_const_zero, zero_add, smul_eq_mul, Pi.zero_apply] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h ((map_ne_zero φ).mpr hm₀)
    rw [hμ0, zero_smul, add_zero] at hsplit
    have hcs : ∀ i : Fin r, c (Fin.castSucc i) = 0 :=
      (Fintype.linearIndependent_iff.mp ih') (fun i => c (Fin.castSucc i)) hsplit
    intro i
    refine Fin.lastCases ?_ (fun j => hcs j) i
    have : c (Fin.last r) = μ - ∑ i : Fin r, c (Fin.castSucc i) * φ (α i) := by
      rw [hμ]; ring
    rw [this, hμ0, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun i _ => by rw [hcs i, zero_mul]

noncomputable def cvec (R : Type*) [CommRing R] (p : PowerSeries ℤ) : ℕ → R := fun j => ((coeff j p : ℤ) : R)

theorem cvec_apply (R : Type*) [CommRing R] (p : PowerSeries ℤ) (j : ℕ) :
    cvec R p j = ((coeff j p : ℤ) : R) := rfl

theorem coeff_map_intCast (R : Type*) [CommRing R] (p : PowerSeries ℤ) (j : ℕ) :
    coeff j (p.map (Int.castRingHom R)) = cvec R p j := by
  rw [coeff_map, eq_intCast]; rfl

theorem coeff_sum_smul_map {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (e : ι → R)
    (p : ι → PowerSeries ℤ) (j : ℕ) :
    coeff j (∑ i ∈ s, e i • (p i).map (Int.castRingHom R)) = ∑ i ∈ s, e i * cvec R (p i) j := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, coeff_map_intCast, smul_eq_mul]

theorem map_sum_smul_map {A R : Type*} [CommRing A] [CommRing R] (ψ : A →+* R) {ι : Type*}
    (s : Finset ι) (e : ι → A) (b : ι → PowerSeries ℤ) :
    (∑ j ∈ s, e j • (b j).map (Int.castRingHom A)).map ψ =
      ∑ j ∈ s, ψ (e j) • (b j).map (Int.castRingHom R) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext m
  rw [coeff_map, coeff_smul, coeff_smul, coeff_map_intCast, coeff_map_intCast, smul_eq_mul,
    smul_eq_mul, map_mul, cvec_apply, cvec_apply, map_intCast]

theorem main
    {L : Type*} [Field L] (A : ValuationSubring L)
    (N : AddSubgroup (PowerSeries ℤ))
    (hN : ∀ (n : ℤ) (p : PowerSeries ℤ), n ≠ 0 → n • p ∈ N → p ∈ N)
    {V : PowerSeries L}
    (hV : V ∈ Submodule.span L ((fun p : PowerSeries ℤ => p.map (Int.castRingHom L)) '' (N : Set (PowerSeries ℤ))))
    (hV0 : V ≠ 0) :
    ∃ (c : L) (u : PowerSeries A), c ≠ 0 ∧
      V = PowerSeries.C c * u.map (A.subtype : A →+* L) ∧
      u.map (IsLocalRing.residue A) ≠ 0 ∧
      u ∈ Submodule.span A
        ((fun p : PowerSeries ℤ => p.map (Int.castRingHom A)) '' (N : Set (PowerSeries ℤ))) := by
  classical
  set kk := IsLocalRing.ResidueField A

  obtain ⟨n, cL, g, hVsum⟩ := Submodule.mem_span_set'.mp hV
  have hg : ∀ i, ∃ p : PowerSeries ℤ, p ∈ N ∧ (p.map (Int.castRingHom L)) = (g i : PowerSeries L) :=
    fun i => by obtain ⟨p, hp, hpe⟩ := (g i).2; exact ⟨p, hp, hpe⟩
  choose p hpN hpg using hg

  set N₀ : Submodule ℤ (PowerSeries ℤ) := Submodule.span ℤ (Set.range p) with hN₀
  have hN₀N : ∀ q ∈ N₀, q ∈ N := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hpN i
    | zero => exact N.zero_mem
    | add x y _ _ hx hy => exact N.add_mem hx hy
    | smul a x _ hx => exact N.zsmul_mem hx a
  set N₁ : Submodule ℤ (PowerSeries ℤ) :=
    { carrier := {q | ∃ D : ℤ, D ≠ 0 ∧ D • q ∈ N₀}
      add_mem' := by
        rintro q q' ⟨D, hD, hq⟩ ⟨D', hD', hq'⟩
        refine ⟨D * D', mul_ne_zero hD hD', ?_⟩
        rw [smul_add]
        refine N₀.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact N₀.smul_mem _ hq
        · rw [mul_smul]; exact N₀.smul_mem _ hq'
      zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact N₀.zero_mem⟩
      smul_mem' := by
        rintro a q ⟨D, hD, hq⟩
        refine ⟨D, hD, ?_⟩
        rw [smul_comm]; exact N₀.smul_mem _ hq } with hN₁
  have hmemN₁ : ∀ q, q ∈ N₁ ↔ ∃ D : ℤ, D ≠ 0 ∧ D • q ∈ N₀ := fun q => Iff.rfl
  have hN₁N : ∀ q ∈ N₁, q ∈ N := by
    intro q hq
    obtain ⟨D, hD, hDq⟩ := (hmemN₁ q).mp hq
    exact hN D q hD (hN₀N _ hDq)
  have hN₁sat : ∀ (m : ℤ) (q : PowerSeries ℤ), m ≠ 0 → m • q ∈ N₁ → q ∈ N₁ := by
    intro m q hm hq
    obtain ⟨D, hD, hDq⟩ := (hmemN₁ _).mp hq
    exact (hmemN₁ q).mpr ⟨D * m, mul_ne_zero hD hm, by rw [mul_smul]; exact hDq⟩
  have hpN₁ : ∀ i, p i ∈ N₁ := fun i =>
    (hmemN₁ _).mpr ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨i, rfl⟩⟩

  let T : ℕ → (Fin n → ℚ) →ₗ[ℚ] ℚ := fun j =>
    { toFun := fun lam => ∑ i, lam i * ((coeff j (p i) : ℤ) : ℚ)
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a x => by simp [Finset.mul_sum, mul_assoc] }
  let E : ℕ → Submodule ℚ (Fin n → ℚ) := fun m => ⨅ j ∈ Finset.range m, LinearMap.ker (T j)
  have hEanti : ∀ m m', m ≤ m' → E m' ≤ E m := by
    intro m m' hmm'
    refine iInf_mono' fun j => ⟨j, iInf_mono' fun hj => ⟨?_, le_rfl⟩⟩
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hmm')
  let Ef : ℕ →o (Submodule ℚ (Fin n → ℚ))ᵒᵈ :=
    ⟨fun m => OrderDual.toDual (E m), fun m m' h => OrderDual.toDual_le_toDual.mpr (hEanti m m' h)⟩
  obtain ⟨m₀, hm₀⟩ := IsArtinian.monotone_stabilizes Ef
  have hstab : ∀ m, m₀ ≤ m → E m₀ = E m := fun m hm => by
    have := hm₀ m hm
    exact OrderDual.toDual.injective this
  have hmemE : ∀ m (lam : Fin n → ℚ), lam ∈ E m ↔ ∀ j < m, ∑ i, lam i * ((coeff j (p i) : ℤ) : ℚ) = 0 := by
    intro m lam
    simp only [E, Submodule.mem_iInf, LinearMap.mem_ker, Finset.mem_range]
    rfl

  have hwindow : ∀ q ∈ N₁, (∀ j < m₀, coeff j q = 0) → q = 0 := by
    intro q hq hzero
    obtain ⟨D, hD, hDq⟩ := (hmemN₁ q).mp hq

    obtain ⟨a, ha⟩ : ∃ a : Fin n → ℤ, D • q = ∑ i, a i • p i := by
      have := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hDq
      obtain ⟨a, ha⟩ := this
      exact ⟨a, ha.symm⟩
    set lam : Fin n → ℚ := fun i => (a i : ℚ) with hlam
    have hcoeffDq : ∀ j, ((coeff j (D • q) : ℤ) : ℚ) = ∑ i, lam i * ((coeff j (p i) : ℤ) : ℚ) := by
      intro j
      rw [ha, map_sum]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, zsmul_eq_mul]; push_cast; rfl
    have hlamE : lam ∈ E m₀ := by
      rw [hmemE]
      intro j hj
      rw [← hcoeffDq j, map_zsmul, hzero j hj, smul_zero, Int.cast_zero]
    have hall : ∀ j, ∑ i, lam i * ((coeff j (p i) : ℤ) : ℚ) = 0 := by
      intro j
      have hj : lam ∈ E (max m₀ (j + 1)) := by rw [← hstab _ (le_max_left _ _)]; exact hlamE
      exact (hmemE _ lam).mp hj j (lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _))
    have hDq0 : D • q = 0 := by
      ext j
      have h1 := hcoeffDq j
      rw [hall j] at h1
      rw [map_zero]
      exact_mod_cast h1
    have hDq0' : PowerSeries.C D * q = 0 := by
      have := hDq0
      rwa [zsmul_eq_mul, show ((D : ℤ) : PowerSeries ℤ) = PowerSeries.C D by simp] at this
    rcases mul_eq_zero.mp hDq0' with h | h
    · exact absurd (by simpa using congrArg (coeff 0) h) hD
    · exact h

  let π : N₁ →ₗ[ℤ] (Fin m₀ → ℤ) :=
    { toFun := fun q j => coeff (j : ℕ) (q : PowerSeries ℤ)
      map_add' := fun x y => by funext j; simp
      map_smul' := fun a x => by
        funext j
        change coeff (j : ℕ) ((a • x : N₁) : PowerSeries ℤ) = a • coeff (j : ℕ) (x : PowerSeries ℤ)
        rw [Submodule.coe_smul, map_zsmul] }
  have hπ : Function.Injective π := by
    intro x y hxy
    apply Subtype.ext
    rw [← sub_eq_zero]
    refine hwindow _ (N₁.sub_mem x.2 y.2) fun j hj => ?_
    have := congrArg (fun f => f ⟨j, hj⟩) hxy
    simp only [π, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [map_sub, this, sub_self]
  haveI : Module.Finite ℤ N₁ := Module.Finite.of_injective π hπ
  haveI : Module.IsTorsionFree ℤ N₁ :=
    Function.Injective.moduleIsTorsionFree π hπ (fun a x => map_smul π a x)
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := N₁)

  have hind : LinearIndependent kk (fun i : Fin r => cvec kk (b i : PowerSeries ℤ)) := by

    have hint : ∀ (m : ℤ) (a : Fin r → ℤ) (w : PowerSeries ℤ), m ≠ 0 →
        ∑ i, a i • (b i : PowerSeries ℤ) = m • w → ∀ i, m ∣ a i := by
      intro m a w hm hw i
      have hwN₁ : w ∈ N₁ := by
        refine hN₁sat m w hm ?_
        rw [← hw]
        exact N₁.sum_mem fun i _ => N₁.smul_mem _ (b i).2

      have hrel : ∑ i, a i • b i = m • (⟨w, hwN₁⟩ : N₁) := by
        apply Subtype.ext
        push_cast
        exact hw
      have := congrArg (fun x => b.repr x i) hrel
      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finsupp.coe_smul,
        Finset.sum_apply, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
      exact ⟨_, this⟩

    obtain ⟨ℓ, hℓ⟩ := CharP.exists kk
    rcases CharP.char_is_prime_or_zero kk ℓ with hprime | hzero
    ·
      haveI : Fact ℓ.Prime := ⟨hprime⟩
      let φ : ZMod ℓ →+* kk := ZMod.castHom (dvd_refl ℓ) kk
      have hF : LinearIndependent (ZMod ℓ) (fun i : Fin r => cvec (ZMod ℓ) (b i : PowerSeries ℤ)) := by
        rw [Fintype.linearIndependent_iff]
        intro a ha

        set at' : Fin r → ℤ := fun i => ((a i).val : ℤ) with hat'
        have hcast : ∀ i, ((at' i : ℤ) : ZMod ℓ) = a i := fun i => by
          simp [hat']

        have hdvd : ∀ j, (ℓ : ℤ) ∣ coeff j (∑ i, at' i • (b i : PowerSeries ℤ)) := by
          intro j
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          have := congrArg (fun f : ℕ → ZMod ℓ => f j) ha
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, cvec] at this
          rw [← this, map_sum, Int.cast_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_zsmul, smul_eq_mul, Int.cast_mul, hcast]
        set w : PowerSeries ℤ := PowerSeries.mk fun j => coeff j (∑ i, at' i • (b i : PowerSeries ℤ)) / ℓ
        have hw : ∑ i, at' i • (b i : PowerSeries ℤ) = (ℓ : ℤ) • w := by
          ext j
          rw [map_zsmul, coeff_mk, smul_eq_mul, Int.mul_ediv_cancel' (hdvd j)]
        have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hprime.ne_zero
        intro i
        obtain ⟨d, hd⟩ := hint ℓ at' w hℓ0 hw i
        rw [← hcast i, hd]
        push_cast
        rw [ZMod.natCast_self, zero_mul]
      have := linearIndependent_comp_ringHom φ r _ hF
      convert this using 2 with i
      funext j
      simp [cvec, φ]
    ·
      haveI : CharP kk 0 := hzero ▸ hℓ
      haveI : CharZero kk := CharP.charP_to_charZero kk
      let φ : ℚ →+* kk := algebraMap ℚ kk
      have hZ : LinearIndependent ℤ (fun i : Fin r => cvec ℤ (b i : PowerSeries ℤ)) := by
        rw [Fintype.linearIndependent_iff]
        intro a ha i
        have hw : ∑ i, a i • (b i : PowerSeries ℤ) = (1 : ℤ) • 0 := by
          rw [one_smul]
          ext j
          rw [map_sum, map_zero]
          have := congrArg (fun f : ℕ → ℤ => f j) ha
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, cvec,
            Int.cast_id] at this
          rw [← this]
          exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, smul_eq_mul]
        obtain ⟨d, hd⟩ := hint 1 a 0 one_ne_zero hw i

        have hrel : ∑ i, a i • b i = 0 := by
          apply Subtype.ext; push_cast; rw [hw, one_smul]
        exact (Fintype.linearIndependent_iff.mp b.linearIndependent) a hrel i
      have hQ : LinearIndependent ℚ (fun i : Fin r => cvec ℚ (b i : PowerSeries ℤ)) := by
        have h1 : LinearIndependent ℤ (fun i : Fin r => cvec ℚ (b i : PowerSeries ℤ)) := by
          let ψ : (ℕ → ℤ) →ₗ[ℤ] (ℕ → ℚ) := Pi.algebraMap ℕ ℤ ℚ
          have hψ : Function.Injective ψ := by
            intro x y hxy; funext j
            have := congrArg (fun f => f j) hxy
            simpa [ψ, Pi.algebraMap] using this
          have hcomp : (fun i : Fin r => cvec ℚ (b i : PowerSeries ℤ)) = ψ ∘ (fun i => cvec ℤ (b i : PowerSeries ℤ)) := by
            funext i j; simp [ψ, cvec, Pi.algebraMap]
          rw [hcomp]
          exact hZ.map' ψ (LinearMap.ker_eq_bot.mpr hψ)
        exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
      have := linearIndependent_comp_ringHom φ r _ hQ
      convert this using 2 with i
      funext j
      simp [cvec, φ]

  have hexp : ∀ i, (p i).map (Int.castRingHom L) =
      ∑ j, ((b.repr ⟨p i, hpN₁ i⟩ j : ℤ) : L) • (b j : PowerSeries ℤ).map (Int.castRingHom L) := by
    intro i
    have h1 : (⟨p i, hpN₁ i⟩ : N₁) = ∑ j, b.repr ⟨p i, hpN₁ i⟩ j • b j := (b.sum_repr _).symm
    have h2 : p i = ∑ j, b.repr ⟨p i, hpN₁ i⟩ j • (b j : PowerSeries ℤ) := by
      have := congrArg (fun x : N₁ => (x : PowerSeries ℤ)) h1
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at this
      exact this
    conv_lhs => rw [h2]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  set e : Fin r → L := fun j => ∑ i, cL i * ((b.repr ⟨p i, hpN₁ i⟩ j : ℤ) : L) with he
  have hVe : V = ∑ j, e j • (b j : PowerSeries ℤ).map (Int.castRingHom L) := by
    rw [← hVsum]
    simp_rw [← hpg, hexp, Finset.smul_sum, ← mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [he, Finset.sum_smul]

  have hr : ∃ j, e j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hV0
    rw [hVe]
    exact Finset.sum_eq_zero fun j _ => by rw [hall j, zero_smul]
  obtain ⟨j₁, hj₁⟩ := hr
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j₁, Finset.mem_univ _⟩
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => A.valuation (e j)) hne
  set c : L := e j₀ with hc
  have hc0 : c ≠ 0 := by
    intro h0
    have := hj₀ j₁ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, _root_.map_eq_zero] at this
    exact hj₁ this
  have he'A : ∀ j, c⁻¹ * e j ∈ A := by
    intro j
    rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
    have hcv : A.valuation c ≠ 0 := by simpa using hc0
    rw [inv_mul_le_one₀ (zero_lt_iff.mpr hcv)]
    exact hj₀ j (Finset.mem_univ _)
  set e' : Fin r → A := fun j => ⟨c⁻¹ * e j, he'A j⟩ with he'
  have he'j₀ : e' j₀ = 1 := Subtype.ext (by simp only [he', hc, OneMemClass.coe_one]; exact inv_mul_cancel₀ hc0)
  set u : PowerSeries A := ∑ j, e' j • (b j : PowerSeries ℤ).map (Int.castRingHom A) with hu
  refine ⟨c, u, hc0, ?_, ?_, ?_⟩
  ·
    rw [hu, map_sum_smul_map, Finset.mul_sum, hVe]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_C_mul, smul_eq_C_mul, ← mul_assoc, ← map_mul]
    congr 2
    simp [he', mul_inv_cancel_left₀ hc0]
  ·
    intro h0
    rw [hu, map_sum_smul_map] at h0
    have hrel : ∑ j, (IsLocalRing.residue A (e' j)) • cvec kk (b j : PowerSeries ℤ) = 0 := by
      funext m
      have := congrArg (fun f : PowerSeries kk => coeff m f) h0
      rw [coeff_sum_smul_map, map_zero] at this
      simpa [Finset.sum_apply] using this
    have hall := (Fintype.linearIndependent_iff.mp hind) _ hrel j₀
    rw [he'j₀, map_one] at hall
    exact one_ne_zero hall
  ·
    rw [hu]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨(b j : PowerSeries ℤ), hN₁N _ (b j).2, rfl⟩

end PowerSeries.SaturationLemmaSpan

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    (N : AddSubgroup (PowerSeries ℤ))
    (hN : ∀ (n : ℤ) (p : PowerSeries ℤ), n ≠ 0 → n • p ∈ N → p ∈ N)
    {V : PowerSeries L}
    (hV : V ∈ Submodule.span L
      ((fun p : PowerSeries ℤ => p.map (Int.castRingHom L)) '' (N : Set (PowerSeries ℤ))))
    (hV0 : V ≠ 0) :
    ∃ (c : L) (u : PowerSeries A), c ≠ 0 ∧
      V = PowerSeries.C c * u.map (A.subtype : A →+* L) ∧
      u.map (IsLocalRing.residue A) ≠ 0 ∧
      u ∈ Submodule.span A
        ((fun p : PowerSeries ℤ => p.map (Int.castRingHom A)) '' (N : Set (PowerSeries ℤ))) :=
  PowerSeries.SaturationLemmaSpan.main A N hN hV hV0

end

end S_PowerSeries_exists_eq_C_mul_map_and_mem_span_of_mem_span_of_saturated
end P2MW
export P2MW.S_PowerSeries_exists_eq_C_mul_map_and_mem_span_of_mem_span_of_saturated (solution)
