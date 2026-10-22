-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.rps_residual_slln
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:21:27.658625+00:00
-- url     : https://prove2.me/submissions/8a842aad-6ab2-4ac0-b432-dfe12fb944b8

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSResidualProcess



namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

section Core

variable {I K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- "nice" primitives: measurable, with randomization variables taking values in `(0,1)`. -/
structure NicePrim (S : Finset (Fin I → ℕ)) (Q : PacketPrimitives I I Ω) : Prop where
  hE : ∀ τ, Measurable (Q.Eincr (τ + 1))
  hU : ∀ τ, Measurable (Q.U (τ + 1))
  hUIoo : ∀ τ ω, Q.U τ ω ∈ Ioo (0 : ℝ) 1
  hunif : ∀ τ, Measure.map (Q.U (τ + 1)) ℙ = volume.restrict (Ioo (0 : ℝ) 1)
  hind : iIndepFun (fun τ : ℕ => Q.U (τ + 1)) ℙ
  hEU : Indep (⨆ τ : ℕ, MeasurableSpace.comap (Q.Eincr (τ + 1)) inferInstance)
      (⨆ τ : ℕ, MeasurableSpace.comap (Q.U (τ + 1)) inferInstance) ℙ
  hf : ∀ z, Measurable (Q.f z)
  hadm : ∀ z u, 0 < u → u < 1 → Q.f z u ∈ S

variable (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ)) (Q : PacketPrimitives I I Ω)

/-- the `toNat` state -/
def Zt (z : Fin I → ℕ) (τ : ℕ) (ω : Ω) : Fin I → ℕ :=
  fun i' => (policyState fr.dat Q z τ ω i').toNat

noncomputable def sh (i : Fin I) (z : Fin I → ℕ) : ℝ := ∫ u in Ioo (0 : ℝ) 1, (Q.f z u i : ℝ)

/-- `G i (z, u) = f(z,u)_i - ŝ_i(z)` -/
noncomputable def Gf (i : Fin I) (p : (Fin I → ℕ) × ℝ) : ℝ := (Q.f p.1 p.2 i : ℝ) - sh Q i p.1

noncomputable def dd (z : Fin I → ℕ) (i : Fin I) (m : ℕ) (ω : Ω) : ℝ :=
  Gf Q i (Zt fr Q z (m - 1) ω, Q.U m ω)

lemma xi_eq_sum (z : Fin I → ℕ) (i : Fin I) (τ : ℕ) (ω : Ω) :
    xi fr Q z i τ ω = ∑ m ∈ Finset.Icc 1 τ, dd fr Q z i m ω := rfl

/-- the bound on the `i`-th component of a schedule -/
def Mb (i : Fin I) : ℕ := S.sup (fun s => s i)

variable {S Q}

lemma f_le (hQ : NicePrim S Q) (i : Fin I) (z : Fin I → ℕ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (Q.f z u i : ℝ) ≤ Mb S i := by
  have := Finset.le_sup (f := fun s : Fin I → ℕ => s i) (hQ.hadm z u hu.1 hu.2)
  exact_mod_cast this

instance : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
  ⟨by simp [Real.volume_Ioo]⟩

lemma f_integrableOn (hQ : NicePrim S Q) (i : Fin I) (z : Fin I → ℕ) :
    IntegrableOn (fun u => (Q.f z u i : ℝ)) (Ioo (0 : ℝ) 1) volume := by
  refine IntegrableOn.of_bound (by simp [Real.volume_Ioo]) ?_ (Mb S i) ?_
  · exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((measurable_pi_apply i).comp (hQ.hf z))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact f_le hQ i z hu

lemma sh_nonneg (i : Fin I) (z : Fin I → ℕ) : 0 ≤ sh Q i z :=
  setIntegral_nonneg measurableSet_Ioo (fun _ _ => Nat.cast_nonneg _)

lemma sh_le (hQ : NicePrim S Q) (i : Fin I) (z : Fin I → ℕ) : sh Q i z ≤ Mb S i := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) 1)
    (f := fun u => (Q.f z u i : ℝ)) (C := Mb S i) (by simp [Real.volume_Ioo])
    (fun u hu => by rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]; exact f_le hQ i z hu)
  rw [measureReal_def, Real.volume_Ioo] at h
  simp at h
  exact le_trans (le_abs_self _) h

lemma Gf_abs_le (hQ : NicePrim S Q) (i : Fin I) (z : Fin I → ℕ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    |Gf Q i (z, u)| ≤ Mb S i := by
  unfold Gf
  rw [abs_le]
  have h1 := f_le hQ i z hu
  have h2 := sh_nonneg (Q := Q) i z
  have h3 := sh_le hQ i z
  have h4 : (0 : ℝ) ≤ Q.f z u i := Nat.cast_nonneg _
  constructor <;> linarith

lemma dd_abs_le (hQ : NicePrim S Q) (z : Fin I → ℕ) (i : Fin I) (m : ℕ) (ω : Ω) :
    |dd fr Q z i m ω| ≤ Mb S i :=
  Gf_abs_le hQ i _ (hQ.hUIoo m ω)

lemma Gf_measurable (hQ : NicePrim S Q) (i : Fin I) : Measurable (Gf Q i) := by
  refine measurable_from_prod_countable_right (fun z => ?_)
  exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((measurable_pi_apply i).comp (hQ.hf z))).sub (measurable_const (a := sh Q i z))

/-- the integral of `Gf i (z, ·)` over `(0,1)` vanishes -/
lemma Gf_integral_zero (hQ : NicePrim S Q) (i : Fin I) (z : Fin I → ℕ) :
    ∫ u in Ioo (0 : ℝ) 1, Gf Q i (z, u) = 0 := by
  have : (fun u => Gf Q i (z, u)) = fun u => (Q.f z u i : ℝ) - sh Q i z := by
    funext u; rfl
  rw [this, integral_sub (f_integrableOn hQ i z) (integrableOn_const (by simp [Real.volume_Ioo]))]
  rw [setIntegral_const, measureReal_def, Real.volume_Ioo]
  simp [sh]

/-- measurability of the state process w.r.t. a sub-σ-algebra containing the primitives -/
lemma policyState_measurable (hQ : NicePrim S Q) (z : Fin I → ℕ) (𝓖 : MeasurableSpace Ω) (N : ℕ)
    (hE : ∀ τ, Measurable[𝓖] (Q.Eincr (τ + 1))) (hU : ∀ τ < N, Measurable[𝓖] (Q.U (τ + 1))) :
    ∀ τ ≤ N, Measurable[𝓖] (policyState fr.dat Q z τ) := by
  intro τ
  induction τ with
  | zero => intro _; exact measurable_const
  | succ τ ih =>
    intro hτ
    have hZ := ih (by omega)
    have hZt : Measurable[𝓖] (Zt fr Q z τ) :=
      (measurable_of_countable (fun v : Fin I → ℤ => fun i' => (v i').toNat)).comp hZ
    have hF : Measurable[𝓖] (fun ω => Q.f (Zt fr Q z τ ω) (Q.U (τ + 1) ω)) :=
      (measurable_from_prod_countable_right (f := fun p : (Fin I → ℕ) × ℝ => Q.f p.1 p.2)
        (fun z' => hQ.hf z')).comp (hZt.prodMk (hU τ (by omega)))
    have heq : policyState fr.dat Q z (τ + 1) = fun ω i =>
        policyState fr.dat Q z τ ω i + ((Q.Eincr (τ + 1) ω i : ℕ) : ℤ)
          - ∑ j, Rint fr.dat i j * ((Q.f (Zt fr Q z τ ω) (Q.U (τ + 1) ω) j : ℕ) : ℤ) := by
      funext ω i
      rfl
    rw [heq]
    refine measurable_pi_iff.mpr (fun i => ?_)
    refine Measurable.sub (Measurable.add ?_ ?_) ?_
    · exact (measurable_pi_apply i).comp hZ
    · exact (measurable_of_countable (fun n : ℕ => (n : ℤ))).comp ((measurable_pi_apply i).comp (hE τ))
    · refine Finset.measurable_sum _ (fun j _ => measurable_const.mul ?_)
      exact (measurable_of_countable (fun n : ℕ => (n : ℤ))).comp ((measurable_pi_apply j).comp hF)

lemma Zt_measurable (hQ : NicePrim S Q) (z : Fin I → ℕ) (𝓖 : MeasurableSpace Ω) (N : ℕ)
    (hE : ∀ τ, Measurable[𝓖] (Q.Eincr (τ + 1))) (hU : ∀ τ < N, Measurable[𝓖] (Q.U (τ + 1)))
    (τ : ℕ) (hτ : τ ≤ N) : Measurable[𝓖] (Zt fr Q z τ) :=
  (measurable_of_countable (fun v : Fin I → ℤ => fun i' => (v i').toNat)).comp
    (policyState_measurable fr hQ z 𝓖 N hE hU τ hτ)

lemma dd_measurable (hQ : NicePrim S Q) (z : Fin I → ℕ) (i : Fin I) (𝓖 : MeasurableSpace Ω) (N : ℕ)
    (hE : ∀ τ, Measurable[𝓖] (Q.Eincr (τ + 1))) (hU : ∀ τ < N, Measurable[𝓖] (Q.U (τ + 1)))
    (m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) : Measurable[𝓖] (dd fr Q z i m) := by
  have hUm : Measurable[𝓖] (Q.U m) := by
    have := hU (m - 1) (by omega)
    rwa [Nat.sub_add_cancel hm] at this
  exact (Gf_measurable hQ i).comp ((Zt_measurable fr hQ z 𝓖 N hE hU (m - 1) (by omega)).prodMk hUm)

/-- ambient measurability of `dd` -/
lemma dd_measurable_amb (hQ : NicePrim S Q) (z : Fin I → ℕ) (i : Fin I) (m : ℕ) (hm : 1 ≤ m) :
    Measurable (dd fr Q z i m) :=
  dd_measurable fr hQ z i _ m (fun τ => hQ.hE τ) (fun τ _ => hQ.hU τ) m hm le_rfl

/-- the family of σ-algebras: `none ↦ σ(E)`, `some τ ↦ σ(U(τ+1))` -/
def mmF (Q : PacketPrimitives I I Ω) : Option ℕ → MeasurableSpace Ω
  | none => ⨆ τ : ℕ, MeasurableSpace.comap (Q.Eincr (τ + 1)) inferInstance
  | some τ => MeasurableSpace.comap (Q.U (τ + 1)) inferInstance

lemma mmF_le (hQ : NicePrim S Q) : ∀ o, mmF Q o ≤ (inferInstance : MeasurableSpace Ω) := by
  intro o
  cases o with
  | none => exact iSup_le (fun τ => (hQ.hE τ).comap_le)
  | some τ => exact (hQ.hU τ).comap_le

lemma mmF_iIndep (hQ : NicePrim S Q) : iIndep (mmF Q) ℙ := by
  classical
  have hind : iIndep (fun τ : ℕ => MeasurableSpace.comap (Q.U (τ + 1)) inferInstance) ℙ := hQ.hind
  rw [iIndep_iff] at hind ⊢
  intro s f hf
  by_cases h : none ∈ s
  · have e1 : (⋂ o ∈ s, f o) = f none ∩ ⋂ τ ∈ s.eraseNone, f (some τ) := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_eraseNone]
      refine ⟨fun H => ⟨H none h, fun τ hτ => H _ hτ⟩, fun H o ho => ?_⟩
      cases o with
      | none => exact H.1
      | some τ => exact H.2 τ ho
    have e2 : ∏ o ∈ s, ℙ (f o) = ℙ (f none) * ∏ τ ∈ s.eraseNone, ℙ (f (some τ)) := by
      rw [← Finset.mul_prod_erase s _ h, ← Finset.map_some_eraseNone, Finset.prod_map]
      rfl
    rw [e1, e2]
    have hB : MeasurableSet[⨆ τ : ℕ, MeasurableSpace.comap (Q.U (τ + 1)) inferInstance]
        (⋂ τ ∈ s.eraseNone, f (some τ)) := by
      refine Finset.measurableSet_biInter _ (fun τ hτ => ?_)
      exact le_iSup (fun τ : ℕ => MeasurableSpace.comap (Q.U (τ + 1)) inferInstance) τ _
        (hf (some τ) (Finset.mem_eraseNone.mp hτ))
    rw [(Indep_iff _ _ _).mp hQ.hEU (f none) _ (hf none h) hB]
    rw [hind s.eraseNone (fun τ hτ => hf (some τ) (Finset.mem_eraseNone.mp hτ))]
  · have e1 : (⋂ o ∈ s, f o) = ⋂ τ ∈ s.eraseNone, f (some τ) := by
      ext ω
      simp only [Set.mem_iInter, Finset.mem_eraseNone]
      refine ⟨fun H τ hτ => H _ hτ, fun H o ho => ?_⟩
      cases o with
      | none => exact absurd ho h
      | some τ => exact H τ ho
    have e2 : ∏ o ∈ s, ℙ (f o) = ∏ τ ∈ s.eraseNone, ℙ (f (some τ)) := by
      have : s = (s.eraseNone).map Function.Embedding.some := by
        rw [Finset.map_some_eraseNone, Finset.erase_eq_of_notMem h]
      conv_lhs => rw [this, Finset.prod_map]
      rfl
    rw [e1, e2]
    exact hind s.eraseNone (fun τ hτ => hf (some τ) (Finset.mem_eraseNone.mp hτ))

/-- the index set of the "past" σ-algebra up to time `k` -/
def Spast (k : ℕ) : Set (Option ℕ) := {o | o = none ∨ ∃ τ, τ < k ∧ o = some τ}

/-- the past σ-algebra `σ(E, U(1), …, U(k))` -/
def Gpast (Q : PacketPrimitives I I Ω) (k : ℕ) : MeasurableSpace Ω := ⨆ o ∈ Spast k, mmF Q o

lemma Gpast_le (hQ : NicePrim S Q) (k : ℕ) : Gpast Q k ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le (fun o _ => mmF_le hQ o)

lemma Gpast_E (k τ : ℕ) : Measurable[Gpast Q k] (Q.Eincr (τ + 1)) := by
  refine measurable_iff_comap_le.mpr (le_trans ?_
    (le_iSup₂ (f := fun o (_ : o ∈ Spast k) => mmF Q o) none (Or.inl rfl)))
  exact le_iSup (fun τ : ℕ => MeasurableSpace.comap (Q.Eincr (τ + 1)) inferInstance) τ

lemma Gpast_U (k τ : ℕ) (hτ : τ < k) : Measurable[Gpast Q k] (Q.U (τ + 1)) := by
  refine measurable_iff_comap_le.mpr
    (le_iSup₂ (f := fun o (_ : o ∈ Spast k) => mmF Q o) (some τ) (Or.inr ⟨τ, hτ, rfl⟩))

lemma indep_past (hQ : NicePrim S Q) (k : ℕ) :
    Indep (Gpast Q k) (MeasurableSpace.comap (Q.U (k + 1)) inferInstance) ℙ := by
  have h := indep_iSup_of_disjoint (mmF_le hQ) (mmF_iIndep hQ)
    (S := Spast k) (T := {some k}) (by
      rw [Set.disjoint_left]
      rintro o ho hT
      rw [Set.mem_singleton_iff] at hT
      subst hT
      rcases ho with h | ⟨τ, hτ, h⟩
      · exact Option.some_ne_none _ h
      · exact absurd (Option.some.inj h) (by omega))
  refine indep_of_indep_of_le_right h ?_
  exact le_iSup₂ (f := fun o (_ : o ∈ ({some k} : Set (Option ℕ))) => mmF Q o) (some k) rfl

/-- orthogonality of the residual increments -/
lemma dd_orth (hQ : NicePrim S Q) (z : Fin I → ℕ) (i : Fin I) {m k : ℕ} (hm : 1 ≤ m)
    (hmk : m < k) : ∫ ω, dd fr Q z i m ω * dd fr Q z i k ω ∂ℙ = 0 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h𝓖le := Gpast_le hQ k'
  have hE : ∀ τ, Measurable[Gpast Q k'] (Q.Eincr (τ + 1)) := fun τ => Gpast_E k' τ
  have hU : ∀ τ < k', Measurable[Gpast Q k'] (Q.U (τ + 1)) := fun τ hτ => Gpast_U k' τ hτ
  have hdm : Measurable[Gpast Q k'] (dd fr Q z i m) := dd_measurable fr hQ z i (Gpast Q k') k' hE hU m hm (by omega)
  have hZt : Measurable[Gpast Q k'] (Zt fr Q z k') := Zt_measurable fr hQ z (Gpast Q k') k' hE hU k' le_rfl
  have hInd := indep_past hQ k'
  -- the decomposition over the countably many values of the state
  let X : (Fin I → ℕ) → Ω → ℝ := fun z' ω => if Zt fr Q z k' ω = z' then dd fr Q z i m ω else 0
  let Y : (Fin I → ℕ) → Ω → ℝ := fun z' ω => Gf Q i (z', Q.U (k' + 1) ω)
  have hXm : ∀ z', Measurable[Gpast Q k'] (X z') := fun z' =>
    Measurable.ite (hZt (measurableSet_singleton z')) hdm measurable_const
  have hXamb : ∀ z', Measurable (X z') := fun z' => (hXm z').mono h𝓖le le_rfl
  have hYm : ∀ z', Measurable[MeasurableSpace.comap (Q.U (k' + 1)) inferInstance] (Y z') :=
    fun z' => (Gf_measurable hQ i).comp
      (measurable_const.prodMk (measurable_iff_comap_le.mpr le_rfl))
  have hYamb : ∀ z', Measurable (Y z') := fun z' =>
    (hYm z').mono (hQ.hU k').comap_le le_rfl
  have hXY : ∀ z', IndepFun (X z') (Y z') ℙ := fun z' =>
    indep_of_indep_of_le_left (indep_of_indep_of_le_right hInd
      (measurable_iff_comap_le.mp (hYm z'))) (measurable_iff_comap_le.mp (hXm z'))
  have hYint : ∀ z', ∫ ω, Y z' ω ∂ℙ = 0 := by
    intro z'
    have h1 : ∫ ω, Y z' ω ∂ℙ = ∫ u, Gf Q i (z', u) ∂(Measure.map (Q.U (k' + 1)) ℙ) := by
      rw [integral_map (hQ.hU k').aemeasurable]
      exact ((Gf_measurable hQ i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    rw [h1, hQ.hunif k']
    exact Gf_integral_zero hQ i z'
  have hpt : ∀ ω, dd fr Q z i m ω * dd fr Q z i (k' + 1) ω = ∑' z', X z' ω * Y z' ω := by
    intro ω
    rw [tsum_eq_single (Zt fr Q z k' ω) (fun z' hz' => by simp [X, Ne.symm hz'])]
    simp only [X, Y, if_true]
    rfl
  have hbound : ∀ z' ω, ‖X z' ω * Y z' ω‖ₑ ≤
      (if Zt fr Q z k' ω = z' then ENNReal.ofReal ((Mb S i : ℝ) * Mb S i) else 0) := by
    intro z' ω
    by_cases hz : Zt fr Q z k' ω = z'
    · rw [if_pos hz, Real.enorm_eq_ofReal_abs, abs_mul]
      apply ENNReal.ofReal_le_ofReal
      have h1 : |X z' ω| ≤ Mb S i := by
        simp only [X, if_pos hz]; exact dd_abs_le fr hQ z i m ω
      have h2 : |Y z' ω| ≤ Mb S i := Gf_abs_le hQ i z' (hQ.hUIoo (k' + 1) ω)
      exact mul_le_mul h1 h2 (abs_nonneg _) (Nat.cast_nonneg _)
    · simp [X, hz]
  have hsum : ∑' z', ∫⁻ ω, ‖X z' ω * Y z' ω‖ₑ ∂ℙ ≠ ∞ := by
    rw [← lintegral_tsum (f := fun z' ω => ‖X z' ω * Y z' ω‖ₑ)
      (fun z' => ((hXamb z').mul (hYamb z')).enorm.aemeasurable)]
    refine ne_top_of_le_ne_top (b := ∫⁻ (_ : Ω), ENNReal.ofReal ((Mb S i : ℝ) * Mb S i) ∂ℙ) ?_ ?_
    · rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
    · refine lintegral_mono (fun ω => ?_)
      calc ∑' z', ‖X z' ω * Y z' ω‖ₑ
          ≤ ∑' z', (if Zt fr Q z k' ω = z' then ENNReal.ofReal ((Mb S i : ℝ) * Mb S i) else 0) :=
            ENNReal.tsum_le_tsum (fun z' => hbound z' ω)
        _ = ENNReal.ofReal ((Mb S i : ℝ) * Mb S i) := by
            rw [tsum_eq_single (Zt fr Q z k' ω) (fun z' hz' => by simp [Ne.symm hz'])]
            simp
  calc ∫ ω, dd fr Q z i m ω * dd fr Q z i (k' + 1) ω ∂ℙ
      = ∫ ω, ∑' z', X z' ω * Y z' ω ∂ℙ := by simp_rw [hpt]
    _ = ∑' z', ∫ ω, X z' ω * Y z' ω ∂ℙ :=
        integral_tsum (fun z' => ((hXamb z').mul (hYamb z')).aestronglyMeasurable) hsum
    _ = ∑' z', (∫ ω, X z' ω ∂ℙ) * ∫ ω, Y z' ω ∂ℙ := by
        congr 1; funext z'
        exact (hXY z').integral_mul_eq_mul_integral (hXamb z').aestronglyMeasurable
          (hYamb z').aestronglyMeasurable
    _ = 0 := by simp [hYint]

/-- the second-moment bound `E[ξ(n)²] ≤ n M²` -/
lemma second_moment (hQ : NicePrim S Q) (z : Fin I → ℕ) (i : Fin I) (n : ℕ) :
    ∫ ω, (xi fr Q z i n ω) ^ 2 ∂ℙ ≤ n * ((Mb S i : ℝ) * Mb S i) := by
  have hint : ∀ m k, 1 ≤ m → 1 ≤ k → Integrable (fun ω => dd fr Q z i m ω * dd fr Q z i k ω) ℙ := by
    intro m k hm hk
    refine Integrable.of_bound ((dd_measurable_amb fr hQ z i m hm).mul
      (dd_measurable_amb fr hQ z i k hk)).aestronglyMeasurable ((Mb S i : ℝ) * Mb S i)
      (Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (dd_abs_le fr hQ z i m ω) (dd_abs_le fr hQ z i k ω) (abs_nonneg _)
      (Nat.cast_nonneg _)
  have heq : ∀ ω, (xi fr Q z i n ω) ^ 2 =
      ∑ m ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, dd fr Q z i m ω * dd fr Q z i k ω := by
    intro ω
    rw [xi_eq_sum, sq, Finset.sum_mul_sum]
  simp_rw [heq]
  rw [integral_finsetSum _ (fun m hm => integrable_finsetSum _ (fun k hk =>
    hint m k (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hk).1))]
  have hrow : ∀ m ∈ Finset.Icc 1 n,
      ∫ ω, ∑ k ∈ Finset.Icc 1 n, dd fr Q z i m ω * dd fr Q z i k ω ∂ℙ ≤ (Mb S i : ℝ) * Mb S i := by
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    rw [integral_finsetSum _ (fun k hk => hint m k hm1 (Finset.mem_Icc.mp hk).1)]
    rw [Finset.sum_eq_single m]
    · calc ∫ ω, dd fr Q z i m ω * dd fr Q z i m ω ∂ℙ
          ≤ ∫ _, (Mb S i : ℝ) * Mb S i ∂ℙ := by
            refine integral_mono (hint m m hm1 hm1) (integrable_const _) (fun ω => ?_)
            have := dd_abs_le fr hQ z i m ω
            have h0 : 0 ≤ (Mb S i : ℝ) := Nat.cast_nonneg _
            nlinarith [abs_nonneg (dd fr Q z i m ω), sq_abs (dd fr Q z i m ω)]
        _ = (Mb S i : ℝ) * Mb S i := by simp
    · intro k hk hkm
      have hk1 := (Finset.mem_Icc.mp hk).1
      rcases lt_or_gt_of_ne hkm with h | h
      · simp_rw [mul_comm (dd fr Q z i m _)]
        exact dd_orth fr hQ z i hk1 h
      · exact dd_orth fr hQ z i hm1 h
    · intro h; exact absurd hm h
  calc ∑ m ∈ Finset.Icc 1 n, ∫ ω, ∑ k ∈ Finset.Icc 1 n, dd fr Q z i m ω * dd fr Q z i k ω ∂ℙ
      ≤ ∑ m ∈ Finset.Icc 1 n, (Mb S i : ℝ) * Mb S i := Finset.sum_le_sum hrow
    _ = n * ((Mb S i : ℝ) * Mb S i) := by simp

lemma xi_measurable (hQ : NicePrim S Q) (z : Fin I → ℕ) (i : Fin I) (n : ℕ) :
    Measurable (xi fr Q z i n) := by
  rw [show xi fr Q z i n = fun ω => ∑ m ∈ Finset.Icc 1 n, dd fr Q z i m ω from rfl]
  exact Finset.measurable_sum _ (fun m hm =>
    dd_measurable_amb fr hQ z i m (Finset.mem_Icc.mp hm).1)

lemma xi_abs_le (hQ : NicePrim S Q) (z : Fin I → ℕ) (i : Fin I) (n : ℕ) (ω : Ω) :
    |xi fr Q z i n ω| ≤ n * Mb S i := by
  rw [xi_eq_sum]
  calc |∑ m ∈ Finset.Icc 1 n, dd fr Q z i m ω|
      ≤ ∑ m ∈ Finset.Icc 1 n, |dd fr Q z i m ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 n, (Mb S i : ℝ) := Finset.sum_le_sum (fun m _ => dd_abs_le fr hQ z i m ω)
    _ = n * Mb S i := by simp

/-- Chebyshev: the probability of a deviation of size `ε` in the `ℓ`-th step -/
lemma dev_bound (hQ : NicePrim S Q) (zseq : ℕ → Fin I → ℕ)
    (hzseq : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 2 ≤ sizeN (zseq ℓ)) (i : Fin I) {ε : ℝ} (hε : 0 < ε)
    (ℓ : ℕ) :
    ℙ {ω | ε ≤ |xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω| / sizeN (zseq ℓ)} ≤
      ENNReal.ofReal (((Mb S i : ℝ) * Mb S i / ε ^ 2) * (1 / ((ℓ : ℝ) + 1) ^ 2)) := by
  have hs1 : ((ℓ : ℝ) + 1) ^ 2 ≤ sizeN (zseq ℓ) := hzseq ℓ
  have hspos : 0 < sizeN (zseq ℓ) := lt_of_lt_of_le (by positivity) hs1
  have hfl : (⌊sizeN (zseq ℓ)⌋₊ : ℝ) ≤ sizeN (zseq ℓ) := Nat.floor_le hspos.le
  have hX2 : ∫ ω, (xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω) ^ 2 ∂ℙ ≤
      sizeN (zseq ℓ) * ((Mb S i : ℝ) * Mb S i) :=
    le_trans (second_moment fr hQ (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊)
      (mul_le_mul_of_nonneg_right hfl (by positivity))
  have hXint : Integrable (fun ω => (xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω) ^ 2) ℙ := by
    refine Integrable.of_bound ((xi_measurable fr hQ _ i _).pow_const 2).aestronglyMeasurable
      (((⌊sizeN (zseq ℓ)⌋₊ : ℝ) * Mb S i) ^ 2) (Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (xi_abs_le fr hQ _ i _ ω) 2
  have hsub : {ω | ε ≤ |xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω| / sizeN (zseq ℓ)} ⊆
      {ω | (ε * sizeN (zseq ℓ)) ^ 2 ≤ (xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω) ^ 2} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [le_div_iff₀ hspos] at hω
    rw [← sq_abs (xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω)]
    exact pow_le_pow_left₀ (by positivity) hω 2
  have hr : (ℙ : Measure Ω).real {ω | (ε * sizeN (zseq ℓ)) ^ 2 ≤ (xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω) ^ 2} ≤
      ((Mb S i : ℝ) * Mb S i / ε ^ 2) * (1 / ((ℓ : ℝ) + 1) ^ 2) := by
    have h1 := mul_meas_ge_le_integral_of_nonneg (μ := ℙ)
      (f := fun ω => (xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω) ^ 2)
      (Eventually.of_forall (fun ω => sq_nonneg _)) hXint ((ε * sizeN (zseq ℓ)) ^ 2)
    have h2 : (ℙ : Measure Ω).real {ω | (ε * sizeN (zseq ℓ)) ^ 2 ≤ (xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω) ^ 2}
        * (ε * sizeN (zseq ℓ)) ^ 2 ≤ sizeN (zseq ℓ) * ((Mb S i : ℝ) * Mb S i) := by
      rw [mul_comm]; exact le_trans h1 hX2
    have hεs : 0 < (ε * sizeN (zseq ℓ)) ^ 2 := by positivity
    set r := (ℙ : Measure Ω).real {ω | (ε * sizeN (zseq ℓ)) ^ 2 ≤ (xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω) ^ 2}
    calc r = r * (ε * sizeN (zseq ℓ)) ^ 2 / (ε * sizeN (zseq ℓ)) ^ 2 := by field_simp
      _ ≤ sizeN (zseq ℓ) * ((Mb S i : ℝ) * Mb S i) / (ε * sizeN (zseq ℓ)) ^ 2 := by gcongr
      _ = ((Mb S i : ℝ) * Mb S i / ε ^ 2) * (1 / sizeN (zseq ℓ)) := by field_simp
      _ ≤ ((Mb S i : ℝ) * Mb S i / ε ^ 2) * (1 / ((ℓ : ℝ) + 1) ^ 2) := by gcongr
  calc ℙ {ω | ε ≤ |xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω| / sizeN (zseq ℓ)}
      ≤ ℙ {ω | (ε * sizeN (zseq ℓ)) ^ 2 ≤ (xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω) ^ 2} :=
        measure_mono hsub
    _ = ENNReal.ofReal ((ℙ : Measure Ω).real {ω | (ε * sizeN (zseq ℓ)) ^ 2 ≤
          (xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω) ^ 2}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hr

/-- the SLLN for nice primitives -/
theorem core_slln (hQ : NicePrim S Q) (zseq : ℕ → Fin I → ℕ)
    (hzseq : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 2 ≤ sizeN (zseq ℓ)) : ℙ (omega2 fr Q zseq) = 1 := by
  have hs : ∀ ℓ, 0 < sizeN (zseq ℓ) := fun ℓ => lt_of_lt_of_le (by positivity) (hzseq ℓ)
  have key : ∀ (i : Fin I) (q : ℕ), ∀ᵐ ω ∂ℙ, ∀ᶠ ℓ in atTop,
      |xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω| / sizeN (zseq ℓ) < 1 / ((q : ℝ) + 1) := by
    intro i q
    have hε : (0 : ℝ) < 1 / ((q : ℝ) + 1) := by positivity
    let A : ℕ → Set Ω := fun ℓ =>
      {ω | 1 / ((q : ℝ) + 1) ≤ |xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω| / sizeN (zseq ℓ)}
    have hsum : ∑' ℓ, ℙ (A ℓ) ≠ ∞ := by
      have hsumm : Summable (fun ℓ : ℕ =>
          ((Mb S i : ℝ) * Mb S i / (1 / ((q : ℝ) + 1)) ^ 2) * (1 / ((ℓ : ℝ) + 1) ^ 2)) := by
        refine Summable.mul_left _ ?_
        have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
        refine this.congr (fun n => ?_)
        push_cast; ring
      refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' ℓ : ℕ,
        ((Mb S i : ℝ) * Mb S i / (1 / ((q : ℝ) + 1)) ^ 2) * (1 / ((ℓ : ℝ) + 1) ^ 2))) ?_
      rw [ENNReal.ofReal_tsum_of_nonneg (fun ℓ => by positivity) hsumm]
      exact ENNReal.tsum_le_tsum (fun ℓ => dev_bound fr hQ zseq hzseq i hε ℓ)
    filter_upwards [ae_finite_setOfPred_mem hsum] with ω hω
    obtain ⟨N, hN⟩ := hω.bddAbove
    rw [eventually_atTop]
    refine ⟨N + 1, fun ℓ hℓ => ?_⟩
    by_contra hcon
    have hmem : ℓ ∈ {ℓ | ω ∈ A ℓ} := not_lt.mp hcon
    have := hN hmem
    omega
  have hall : ∀ᵐ ω ∂ℙ, ∀ (i : Fin I) (q : ℕ), ∀ᶠ ℓ in atTop,
      |xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω| / sizeN (zseq ℓ) < 1 / ((q : ℝ) + 1) := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact key i
  have hmem : ∀ᵐ ω ∂ℙ, ω ∈ omega2 fr Q zseq := by
    filter_upwards [hall] with ω hω
    intro i
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨q, hq⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hω i q)
    refine ⟨N, fun ℓ hℓ => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (hs ℓ)]
    exact lt_trans (hN ℓ hℓ) hq
  rw [← measure_univ (μ := (ℙ : Measure Ω))]
  apply measure_congr
  rw [ae_eq_univ]
  exact ae_iff.mp hmem

end Core

section Transfer

variable {I K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

noncomputable def clamp (x : ℝ) : ℝ := if x ∈ Ioo (0 : ℝ) 1 then x else 1 / 2

lemma clamp_mem (x : ℝ) : clamp x ∈ Ioo (0 : ℝ) 1 := by
  unfold clamp
  split_ifs with h
  · exact h
  · constructor <;> norm_num

lemma clamp_measurable : Measurable clamp :=
  Measurable.ite measurableSet_Ioo measurable_id measurable_const

noncomputable def mkE (P : PacketPrimitives I I Ω) (h : ∀ τ, AEMeasurable (P.Eincr (τ + 1)) ℙ) :
    ℕ → Ω → Fin I → ℕ
  | 0 => fun _ _ => 0
  | τ + 1 => (h τ).mk _

noncomputable def mkU (P : PacketPrimitives I I Ω) (h : ∀ τ, AEMeasurable (P.U (τ + 1)) ℙ) :
    ℕ → Ω → ℝ
  | 0 => fun _ => 1 / 2
  | τ + 1 => fun ω => clamp ((h τ).mk _ ω)

noncomputable def niceOf (P : PacketPrimitives I I Ω) (hE : ∀ τ, AEMeasurable (P.Eincr (τ + 1)) ℙ)
    (hU : ∀ τ, AEMeasurable (P.U (τ + 1)) ℙ) : PacketPrimitives I I Ω :=
  ⟨P.f, mkE P hE, mkU P hU⟩

lemma policyState_congr {dat : PacketNetworkData I I} {P Q : PacketPrimitives I I Ω}
    (hf : P.f = Q.f) (z : Fin I → ℕ) (ω : Ω)
    (h : ∀ τ, P.Eincr (τ + 1) ω = Q.Eincr (τ + 1) ω ∧ P.U (τ + 1) ω = Q.U (τ + 1) ω) :
    ∀ τ, policyState dat P z τ ω = policyState dat Q z τ ω
  | 0 => rfl
  | τ + 1 => by
    have ih := policyState_congr (dat := dat) hf z ω h τ
    show nextState dat (policyState dat P z τ ω) (P.Eincr (τ + 1) ω)
        (P.f (fun i => (policyState dat P z τ ω i).toNat) (P.U (τ + 1) ω)) =
      nextState dat (policyState dat Q z τ ω) (Q.Eincr (τ + 1) ω)
        (Q.f (fun i => (policyState dat Q z τ ω i).toNat) (Q.U (τ + 1) ω))
    rw [ih, (h τ).1, (h τ).2, hf]

lemma xi_congr (fr : FixedRoutingData I K) {P Q : PacketPrimitives I I Ω} (hf : P.f = Q.f)
    (z : Fin I → ℕ) (i : Fin I) (τ : ℕ) (ω : Ω)
    (h : ∀ τ, P.Eincr (τ + 1) ω = Q.Eincr (τ + 1) ω ∧ P.U (τ + 1) ω = Q.U (τ + 1) ω) :
    xi fr P z i τ ω = xi fr Q z i τ ω := by
  unfold xi policySched shat
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm1 := (Finset.mem_Icc.mp hm).1
  have hU : P.U m ω = Q.U m ω := by
    have := (h (m - 1)).2
    rwa [Nat.sub_add_cancel hm1] at this
  rw [policyState_congr hf z ω h (m - 1), hU, hf]

lemma iSup_comap_eq_comap_pi {Ω : Type*} {β : Type*} [MeasurableSpace β] (g : ℕ → Ω → β) :
    (⨆ τ : ℕ, MeasurableSpace.comap (g τ) inferInstance) =
      MeasurableSpace.comap (fun ω τ => g τ ω) MeasurableSpace.pi := by
  show _ = MeasurableSpace.comap (fun ω τ => g τ ω)
    (⨆ τ : ℕ, MeasurableSpace.comap (fun b : ℕ → β => b τ) inferInstance)
  rw [MeasurableSpace.comap_iSup]
  simp_rw [MeasurableSpace.comap_comp]
  rfl

theorem rps_residual_slln_core
    (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ)) (hS : IsScheduleSet fr.cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω) (hP : PrimitiveAssumptions P lam)
    (hRPS : IsRPSPolicy fr S P.f)
    (zseq : ℕ → Fin I → ℕ) (hzseq : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 2 ≤ sizeN (zseq ℓ)) :
    ℙ (omega2 fr P zseq) = 1 := by
  have hEae : ∀ τ, AEMeasurable (P.Eincr (τ + 1)) ℙ := fun τ =>
    (hP.arrivals_ident τ).aemeasurable_fst
  have hUae : ∀ τ, AEMeasurable (P.U (τ + 1)) ℙ := fun τ => by
    by_contra h
    have h1 := hP.uniform τ
    rw [Measure.map_of_not_aemeasurable h] at h1
    have h2 := congrArg (fun μ : Measure ℝ => μ univ) h1
    simp [Real.volume_Ioo] at h2
  have hUIoo : ∀ τ, ∀ᵐ ω ∂ℙ, P.U (τ + 1) ω ∈ Ioo (0 : ℝ) 1 := fun τ => by
    rw [ae_iff]
    have : {ω | ¬ P.U (τ + 1) ω ∈ Ioo (0 : ℝ) 1} = P.U (τ + 1) ⁻¹' (Ioo 0 1)ᶜ := rfl
    rw [this, ← Measure.map_apply_of_aemeasurable (hUae τ) measurableSet_Ioo.compl, hP.uniform τ,
      Measure.restrict_apply measurableSet_Ioo.compl, compl_inter_self, measure_empty]
  set Q : PacketPrimitives I I Ω := niceOf P hEae hUae with hQdef
  have hQE : ∀ τ, P.Eincr (τ + 1) =ᵐ[ℙ] Q.Eincr (τ + 1) := fun τ => (hEae τ).ae_eq_mk
  have hQU : ∀ τ, P.U (τ + 1) =ᵐ[ℙ] Q.U (τ + 1) := fun τ => by
    filter_upwards [(hUae τ).ae_eq_mk, hUIoo τ] with ω h1 h2
    show P.U (τ + 1) ω = clamp ((hUae τ).mk _ ω)
    rw [← h1, clamp, if_pos h2]
  have hallE : ∀ᵐ ω ∂ℙ, ∀ τ, P.Eincr (τ + 1) ω = Q.Eincr (τ + 1) ω := by
    rw [ae_all_iff]; exact hQE
  have hallU : ∀ᵐ ω ∂ℙ, ∀ τ, P.U (τ + 1) ω = Q.U (τ + 1) ω := by
    rw [ae_all_iff]; exact hQU
  have hQ : NicePrim S Q :=
    { hE := fun τ => (hEae τ).measurable_mk
      hU := fun τ => clamp_measurable.comp (hUae τ).measurable_mk
      hUIoo := by
        intro τ ω
        cases τ with
        | zero =>
          show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1
          constructor <;> norm_num
        | succ τ => exact clamp_mem _
      hunif := fun τ => by
        rw [← Measure.map_congr (hQU τ)]; exact hP.uniform τ
      hind := by
        rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
        have h0 := iIndepFun_iff_measure_inter_preimage_eq_mul.mp hP.uniform_indep
        intro s sets hsets
        have e1 : (⋂ τ ∈ s, Q.U (τ + 1) ⁻¹' sets τ) =ᵐ[ℙ] (⋂ τ ∈ s, P.U (τ + 1) ⁻¹' sets τ) := by
          rw [Filter.eventuallyEq_set]
          filter_upwards [hallU] with ω hω
          simp only [Set.mem_iInter, Set.mem_preimage, hω]
        rw [measure_congr e1, h0 s hsets]
        refine Finset.prod_congr rfl (fun τ _ => measure_congr ?_)
        rw [Filter.eventuallyEq_set]
        filter_upwards [hQU τ] with ω hω
        simp [hω]
      hEU := by
        rw [iSup_comap_eq_comap_pi, iSup_comap_eq_comap_pi]
        have h0 := hP.arrivals_uniform_indep
        rw [iSup_comap_eq_comap_pi, iSup_comap_eq_comap_pi] at h0
        have h1 : IndepFun (fun ω τ => P.Eincr (τ + 1) ω) (fun ω τ => P.U (τ + 1) ω) ℙ := h0
        have hjE : (fun ω τ => P.Eincr (τ + 1) ω) =ᵐ[ℙ] (fun ω τ => Q.Eincr (τ + 1) ω) :=
          hallE.mono (fun ω hω => funext hω)
        have hjU : (fun ω τ => P.U (τ + 1) ω) =ᵐ[ℙ] (fun ω τ => Q.U (τ + 1) ω) :=
          hallU.mono (fun ω hω => funext hω)
        exact h1.congr hjE hjU
      hf := hP.policy_measurable
      hadm := fun z u h0 h1 => (hRPS.1 z u h0 h1).1 }
  have hcore := core_slln fr hQ zseq hzseq
  rw [← hcore]
  apply measure_congr
  have hall : ∀ᵐ ω ∂ℙ, ∀ τ, P.Eincr (τ + 1) ω = Q.Eincr (τ + 1) ω ∧ P.U (τ + 1) ω = Q.U (τ + 1) ω := by
    filter_upwards [hallE, hallU] with ω h1 h2
    exact fun τ => ⟨h1 τ, h2 τ⟩
  rw [Filter.eventuallyEq_set]
  filter_upwards [hall] with ω hω
  simp only [omega2, Set.mem_ofPred_eq]
  have hx : ∀ ℓ i, xi fr P (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω = xi fr Q (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω :=
    fun ℓ i => xi_congr fr (P := P) (Q := Q) rfl (zseq ℓ) i _ ω hω
  refine forall_congr' (fun i => ?_)
  simp_rw [hx]

end Transfer

end ProcessingNetworks.PacketNetworks

open ProcessingNetworks.PacketNetworks
open MeasureTheory ProbabilityTheory

theorem solution
    {I K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ)) (hS : IsScheduleSet fr.cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω) (hP : PrimitiveAssumptions P lam)
    (hRPS : IsRPSPolicy fr S P.f)
    (zseq : ℕ → Fin I → ℕ) (hzseq : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 2 ≤ sizeN (zseq ℓ)) :
    ℙ (omega2 fr P zseq) = 1 := by
  exact rps_residual_slln_core fr S hS lam P hP hRPS zseq hzseq
